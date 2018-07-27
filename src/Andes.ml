
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
    Fmt.fprintf out "(@[solution@ :subst {@[%a@]}@ :constraint %a@])"
      Fmt.(seq ~sep:(return "@ ") @@ within "(" ")" @@ hbox @@ pair ~sep:(return "@ := ") Var.pp Term.pp)
      (Var.Map.to_seq s.subst)
      (Fmt.Dump.list Term.pp) s.constr
end

type goal = Term.t list

module Config = struct
  type t = {
    max_step: int;
    progress: bool;
  }

  let pp out { max_step; progress } =
    Format.fprintf out "(@[config@ :max_steps %d@ :progress %B@])"
      max_step progress

  let set_progress progress c = {c with progress}
  let set_max_steps max_step c = {c with max_step}
  let default : t = {max_step=max_int; progress=false}
end

(** {2 Main State of the Algorithm} *)
module Solver : sig
  type t

  val make : ?config:Config.t -> goal -> t

  val next_solution : t -> Solution.t option
end = struct
  type tree_kind = Tree_dead | Tree_root | Tree_open

  type tree = {
    t_id: int; (* unique id *)
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
    e_solutions: Clause.t Vec.vector;
    e_listeners: tree Vec.vector;
  }

  (* if true, can be dropped from listeners *)
  let[@inline] tree_is_dead (t:tree) = t.t_kind = Tree_dead

  let pp_tree out (t:tree) =
    let pp_label out = function
      | L_none -> Fmt.string out ":no-label"
      | L_solution -> Fmt.string out ":solution"
      | L_defer {entry;offset;_} ->
        Fmt.fprintf out "@[<2>:defer[%d] (@[goal %a@])@]"
          offset (Util.pp_iarray Term.pp) entry.e_goal
      | L_program { term; _ } ->
        Fmt.fprintf out ":program %a" Term.pp term
    in
    Fmt.fprintf out "(@[tree[%d]@ :label %a@ :clause %a@])"
      t.t_id pp_label t.t_label Clause.pp t.t_clause

  (* TODO: indexing for same-length matching (feature vector?) *)
  type t = {
    tbl: tbl_entry Vec.vector;
    config: Config.t;
    root: tbl_entry; (* first entry *)
    tasks: tree Queue.t; (* trees to expand *)
    mutable n_tasks: int;
  }

  let[@inline] n_root_sols (s:t) : int = Vec.size s.root.e_solutions
  let[@inline] has_task s = not @@ Queue.is_empty s.tasks
  let[@inline] next_task s = s.n_tasks <- s.n_tasks - 1; Queue.pop s.tasks
  let[@inline] push_task s q = s.n_tasks <- 1 + s.n_tasks; Queue.push q s.tasks
  let[@inline] n_tasks s = s.n_tasks

  let pp_progress_ (st:t) : unit =
    Util.Status.printf "entries %d | tasks %d | solutions %d"
      (Vec.length st.tbl)
      (n_tasks st)
      (Vec.length st.root.e_solutions)

  let pp_progress st = if st.config.Config.progress then pp_progress_ st

  let mk_tree =
    let n = ref 0 in
    fun ?(kind=Tree_open) (e:tbl_entry) (c:Clause.t) : tree option ->
      match Simplify.simplify_c c with
      | None -> None
      | Some c ->
        incr n;
        Some { t_id= !n; t_clause=c; t_label=L_none; t_kind=kind; t_entry=e }

  (* TODO: support abstraction function for entries:
     - need to see if abstraction exists already (just use it instead then)
     - otherwise proceed as usual, but handle cases where solutions
       do not actually unify with proper goal
  *)

  (* is [c] a solution?
     TODO: extend once we have constraints (i.e accept if the whole guard is
     a conjunction of satisfiable constraints)
  *)
  let is_solution_c (c:Clause.t) : bool =
    IArray.for_all
      (fun t -> match Term.view t with
         | Term.Eqn {sign=false; lhs; rhs} when not (Term.equal lhs rhs) -> true
         | _ -> false)
      (Clause.guard c)

  (* this tree is either a solution, or dead, for no other rule applies to it.
     Mark it accordingly and notify other entries if it's a solution *)
  let tree_solution_or_dead (st:t) (t:tree) : unit =
    assert (t.t_label = L_none);
    if t.t_kind = Tree_dead then ()
    else if is_solution_c t.t_clause then (
      Log.logf 5 (fun k->k "(@[tree.is_solution@ %a@])" pp_tree t);
      (* add to solutions *)
      t.t_label <- L_solution;
      Vec.push t.t_entry.e_solutions t.t_clause;
      (* notify listeners *)
      Vec.iter (push_task st) t.t_entry.e_listeners
    ) else (
      t.t_kind <- Tree_dead;
      (* XXX: actually correct? just drop the tree? *)
      Util.errorf "tree %a@ should be dead or a solution"
        pp_tree t
    )

  (* Label a single tree. We assume that the clause is simplified already. *)
  let process_tree (st:t) (tree:tree) : unit =
    Log.logf 2 (fun k->k "(@[@{<yellow>process_tree@}@ %a@])" pp_tree tree);
    assert (tree.t_label = L_none);
    let c = tree.t_clause in
    let undo = Undo_stack.create() in
    (* find if some other entry subsumes part of the clause's guard?
       TODO: indexing to make this fast *)
    let find_existing () : (Term.t IArray.t * tbl_entry) option =
      Vec.to_seq st.tbl
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
    let find_function () : _ option =
      IArray.to_seq c.Clause.guard
      |> Sequence.zip_i
      |> Sequence.find_map
        (fun (i,t) -> match Term.view t with
           | Term.App {f; _} ->
             begin match Fun.kind f with
               | F_defined{rules} when rules<>[] -> Some (i,f,rules,t)
               | _ -> None
             end
           | _ -> None)
    in
    (* perform resolution *)
    let do_resolution (i:int) f (rules:_ list) (t:Term.t) : unit =
      Log.logf 4 (fun k->k "(@[@{<yellow>do_resolution@}@ :term %a@])" Term.pp t);
      let guard =
        let a = c.Clause.guard in
        IArray.init (IArray.length a-1)
          (fun j -> if j<i then IArray.get a j else IArray.get a (j+1))
      in
      tree.t_label <- L_program {term=t; fun_=f};
      let undo = Undo_stack.create() in
      List.iter
        (fun r ->
           Log.logf 5 (fun k->k "(@[do_resolution.step@ :rule %a@ :term %a@])" Rule.pp r Term.pp t);
           let c' =
             Undo_stack.with_ ~undo
               (fun undo ->
                  try
                    Unif.unify ~undo t (Rule.concl r);
                    let c' =
                      Clause.make c.Clause.concl (IArray.append guard @@ Rule.body r)
                      |> Clause.deref_deep
                      |> Clause.rename
                    in
                    Some c'
                  with Unif.Fail -> None)
           in
           match CCOpt.flat_map (mk_tree ~kind:Tree_open tree.t_entry) c' with
           | None -> ()
           | Some tree' ->
             Log.logf 5 (fun k->k "(@[resolution-yields@ %a@])" Clause.pp tree'.t_clause);
             push_task st tree';
        )
        rules
    in
    match tree.t_kind with
    | Tree_dead -> ()
    | Tree_open ->
      begin match find_existing () with
        | Some (subgoal, entry) ->
          Log.logf 4 (fun k->k "(@[@{<yellow>defer-to@}@ %a@])" (pp_iarray Term.pp) entry.e_goal);
          Vec.push entry.e_listeners tree;
          tree.t_label <- L_defer {entry; goal=subgoal; offset=0;};
          (* TODO: do resolution right now if entry has solutions *)
        | None ->
          begin match find_function () with
            | None -> tree_solution_or_dead st tree
            | Some (i,f,rs,t) -> do_resolution i f rs t
          end
      end
    | Tree_root ->
      (* do not look for a node to defer to at the root *)
      begin match find_function () with
        | None -> tree_solution_or_dead st tree
        | Some (i,f,rs,t) -> do_resolution i f rs t
      end

  (* process tasks until we find a new solution *)
  let next_ (st:t) : Clause.t option =
    let n_sols0 = n_root_sols st in
    while n_root_sols st = n_sols0 && has_task st do
      pp_progress st;
      let tree = next_task st in
      process_tree st tree
    done;
    Util.Status.flush();
    (* if new solution was found, return it *)
    if n_root_sols st > n_sols0 then (
      Some (Vec.get st.root.e_solutions n_sols0)
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
      e_solutions=Vec.create();
      e_listeners=Vec.create();
    } in
    let s = {
      tbl=Vec.return entry; config; root=entry; tasks=Queue.create(); n_tasks=0;
    } in
    (* see if the original clause is not absurd *)
    begin match mk_tree ~kind:Tree_root entry c with
      | None -> ()
      | Some tree ->
        (* need to process this new [tree] *)
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
