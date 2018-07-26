
(** {1 Logic Programming Tool} *)

open Util
open Types

module ID = ID
module Term = Term
module Var = Var
module Fun = Fun
module Rule = Types.Rule
module Types = Types
module Simplify = Simplify

module Log = Util.Log

module Solution = struct
  type t = {
    subst: Term.t Var.Map.t;
    constr: Term.t list; (* constraints *)
  }

  let pp out s =
    Fmt.fprintf out "(@[solution@ :subst %a@ :constraint %a@])"
      (Fmt.seq ~sep:(Fmt.return "@ ") @@ Fmt.hbox @@ Fmt.Dump.pair Var.pp Term.pp)
      (Var.Map.to_seq s.subst)
      (Fmt.Dump.list Term.pp) s.constr
end

type goal = Term.t list

module Config = struct
  type t = {
    max_step: int;
  }

  let pp out c =
    Format.fprintf out "(@[config@ :max_steps %d@])" c.max_step

  let default : t = {max_step=max_int}
end

(** {2 Main State of the Algorithm} *)
module Solver : sig
  type t

  val make : ?config:Config.t -> goal -> t

  val next_solution : t -> Solution.t option
end = struct
  type tree_kind = Tree_dead | Tree_root | Tree_open

  type tree = {
    t_clause: Clause.t;
    mutable t_label: label;
    mutable t_kind: tree_kind;
    t_entry: tbl_entry;
  }

  and label =
    | L_none
    | L_solution (* leaf *)
    | L_program of {
        term: Term.t;
        fun_: Fun.t; (* program of this function *)
      }
    | L_defer of {
        entry: tbl_entry; (* where solutions come from *)
        goal: Term.t IArray.t; (* the part of the clause's guard that we defer *)
        mutable offset: int;  (* offset in solutions *)
      } (* re-use solutions of this *)

  and tbl_entry = {
    e_goal: Term.t IArray.t;
    e_tree: tree Vec.vector;
    e_solutions: Clause.t Vec.vector;
    e_listeners: tree Vec.vector;
  }

  (* if true, can be dropped from listeners *)
  let[@inline] tree_is_dead (t:tree) = t.t_kind = Tree_dead

  (* TODO: indexing for same-length matching (feature vector?) *)
  type t = {
    tbl: tbl_entry Vec.vector;
    config: Config.t;
    root: tbl_entry; (* first entry *)
    tasks: tree Queue.t; (* trees to expand *)
  }

  let[@inline] n_root_sols (s:t) : int = Vec.size s.root.e_solutions
  let[@inline] has_task s = not @@ Queue.is_empty s.tasks
  let[@inline] next_task s = Queue.pop s.tasks

  let mk_tree ?(kind=Tree_open) (e:tbl_entry) (c:Clause.t) : tree option =
    match Simplify.simplify_c c with
    | None -> None
    | Some c -> Some { t_clause=c; t_label=L_none; t_kind=kind; t_entry=e }

  (* TODO: support abstraction function for entries:
     - need to see if abstraction exists already (just use it instead then)
     - otherwise proceed as usual, but handle cases where solutions
     do not actually unify with proper goal
  *)

  (* this tree is either a solution, or dead. Mark it accordingly
     and notify other entries *)
  let tree_solution_or_dead (s:t) (t:tree) : unit =
    assert (t.t_label = L_none);
    t.t_label <- L_solution
  (* TODO: check if really a solution.
     - if yes, add itself to entry.solutions, then notify listeners
     - otherwise mark as dead *)

  (* Label a single tree. We assume that the clause is simplified already. *)
  let process_tree (s:t) (t:tree) : unit =
    assert (t.t_label = L_none);
    let c = t.t_clause in
    Log.logf 3 (fun k->k "(@[process_tree@ %a@])" Clause.pp c);
    let undo = Undo_stack.create() in
    (* find if some other entry subsumes part of the clause's guard?
       TODO: indexing to make this fast *)
    let find_existing () : (Term.t IArray.t * tbl_entry) option =
      Vec.to_seq s.tbl
      |> Sequence.find_map
        (fun entry ->
           (* use [entry] iff it matches some lit of the clause's guard *)
           (* TODO: be able to multi-match *)
           if IArray.length entry.e_goal = 1 then (
             (* look in the body of clause *)
             IArray.to_seq c.Clause.guard
             |> Sequence.find_map
               (fun t ->
                  Undo_stack.with_ ~undo (fun undo ->
                    try
                      Unif.match_ ~undo (IArray.get entry.e_goal 0) t;
                      Some (IArray.singleton t, entry)
                    with Unif.Fail -> None))
           ) else None)
    in
    (* find a member of the clause's guard that is eligible for resolution *)
    let find_function () : Term.t option =
      assert false (* TODO *)
    in
    match t.t_kind with
    | Tree_dead -> ()
    | Tree_open ->
      begin match find_existing () with
        | Some (subgoal, entry) ->
          Vec.push entry.e_listeners t;
          t.t_label <- L_defer {entry; goal=subgoal; offset=0;};
        | None ->
          begin match find_function () with
            | None -> tree_solution_or_dead s t
            | Some t -> assert false (* TODO: t should be expanded by resolution *)
          end
      end
    | Tree_root ->
      (* do not look for a node to defer to at the root *)
      begin match find_function () with
        | None -> tree_solution_or_dead s t
        | Some t -> assert false (* TODO: t should be expanded by resolution *)
      end

  (* process tasks until we find a new solution *)
  let next_ (s:t) : Clause.t option =
    let n_sols0 = n_root_sols s in
    while n_root_sols s = n_sols0 && has_task s do
      let tree = next_task s in
      process_tree s tree
    done;
    (* if new solution was found, return it *)
    if n_root_sols s > n_sols0 then (
      Some (Vec.get s.root.e_solutions n_sols0)
    ) else None

  let sol_of_clause (s:t) (c:Clause.t) : Solution.t =
    let goal = s.root.e_goal in
    let vars = Term.vars_seq (IArray.to_seq goal) in
    let map =
      Undo_stack.with_ (fun undo ->
        assert (IArray.length goal = IArray.length (Clause.concl c));
        try
          IArray.iter2 (Unif.unify ~undo) goal (Clause.concl c);
          Var.Set.to_seq vars
          |> Sequence.map (fun v -> v, Term.deref_deep (Term.var v))
          |> Var.Map.of_seq
        with Unif.Fail -> assert false)
    in
    {Solution.subst=map; constr=IArray.to_list @@ Clause.guard c}

  (* convert a clause into a {!solution} *)
  let next_solution s : Solution.t option =
    CCOpt.map (sol_of_clause s) (next_ s)

  (* make a new solver for the given goal *)
  let make ?(config=Config.default) (g:goal) : t =
    assert (g <> []);
    let g = IArray.of_list g in
    let c = Clause.make g g in
    let entry = {
      e_goal=g;
      e_tree=Vec.create();
      e_solutions=Vec.create();
      e_listeners=Vec.create();
    } in
    let s = {
      tbl=Vec.return entry; config; root=entry; tasks=Queue.create();
    } in
    (* see if the original clause is not absurd *)
    begin match mk_tree ~kind:Tree_root entry c with
      | None -> ()
      | Some tree ->
        (* need to process this new [tree] *)
        Vec.push entry.e_tree tree;
        Queue.push tree s.tasks;
    end;
    s
end

let solve ?config (g:goal) : Solution.t option =
  let s = Solver.make ?config g in
  Solver.next_solution s


(**/**)
module Fmt = CCFormat
module Util = Util
module IArray = IArray
(**/**)
