
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
      Fmt.(iter ~sep:(return "@ ") @@ within "(" ")" @@ hbox @@ pair ~sep:(return "@ := ") Var.pp Term.pp)
      (Var.Map.to_iter s.subst)
      (Fmt.Dump.list Term.pp) s.constr
end

type goal = Term.t list

module Config = struct
  type t = {
    max_step: int;
  }

  let pp out { max_step; } =
    Format.fprintf out "(@[config@ :max_steps %d@])"
      max_step

  let set_max_steps max_step _c = {max_step}
  let default : t = {max_step=max_int; }
end

(** {2 Main State of the Algorithm} *)
module Solver : sig
  type t

  val make : ?config:Config.t -> goal -> t

  val next_solution : t -> Solution.t option * int
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
        goal: Term.t; (* the part of the clause's guard that we defer *)
        goal_idx: int; (* index of goal in the clause's guard *)
        mutable offset: int;  (* offset in solutions *)
      } (* re-use solutions of this *)

  and tbl_entry = {
    e_goal: Term.t Array.t;
    e_solutions: Clause.t Vec.vector;
    e_listeners: tree Vec.vector;
  }

  let pp_tree out (t:tree) =
    let pp_label out = function
      | L_none -> Fmt.string out ":no-label"
      | L_solution -> Fmt.string out ":solution"
      | L_defer {entry;offset;_} ->
        Fmt.fprintf out "@[<2>:defer[%d] (@[goal %a@])@]"
          offset (Util.pp_array Term.pp) entry.e_goal
      | L_program { term; _ } ->
        Fmt.fprintf out ":program %a" Term.pp term
    in
    Fmt.fprintf out "(@[tree[%d%s]@ :label %a@ :clause %a@])"
      t.t_id (if t.t_kind=Tree_root then "/root" else "")
      pp_label t.t_label Clause.pp t.t_clause

  (* TODO: indexing for same-length matching (feature vector?) *)
  type t = {
    tbl: tbl_entry Vec.vector;
    config: Config.t;
    root: tbl_entry; (* first entry *)
    tasks: tree Queue.t; (* trees to expand *)
    mutable n_tasks: int;
    mutable n_steps: int;
  }

  let[@inline] n_root_sols (s:t) : int = Vec.size s.root.e_solutions
  let[@inline] has_task s = not @@ Queue.is_empty s.tasks
  let[@inline] next_task s = s.n_tasks <- s.n_tasks - 1; Queue.pop s.tasks
  let[@inline] push_task s q = s.n_tasks <- 1 + s.n_tasks; Queue.push q s.tasks
  let[@inline] n_tasks s = s.n_tasks

  let pp_progress (st:t) : unit =
    Util.Status.printf "steps %d | entries %d | tasks %d | solutions %d"
      st.n_steps
      (Vec.length st.tbl)
      (n_tasks st)
      (Vec.length st.root.e_solutions)

  let mk_tree =
    let n = ref 0 in
    fun ?(kind=Tree_open) (e:tbl_entry) (c:Clause.t) : tree option ->
      match Simplify.simplify_c c with
      | None -> None
      | Some c ->
        incr n;
        Some { t_id= !n; t_clause=c; t_label=L_none; t_kind=kind; t_entry=e }

  let mk_entry g : tbl_entry =
    { e_goal=g; e_solutions=Vec.create(); e_listeners=Vec.create(); }

  (* TODO: support abstraction function for entries:
     - need to see if abstraction exists already (just use it instead then)
     - otherwise proceed as usual, but handle cases where solutions
       do not actually unify with proper goal
  *)

  let is_constraint (t:Term.t) : bool =
    match Term.view t with
    | Term.Eqn {sign=false; lhs; rhs} when not (Term.equal lhs rhs) -> true
    | _ -> false

  (* TODO: extend once we have proper decision procedures for extensible constraints *)
  let sat_constraints (_cs:Term.t Array.t) : bool = true

  (* is [c] a solution? *)
  let is_solution_c (c:Clause.t) : bool =
    Array.for_all is_constraint (Clause.guard c) &&
    sat_constraints (Clause.guard c)

  (* find if some other entry subsumes this goal exactly
     TODO: goal with multiple terms?
     TODO: indexing to make this fast *)
  let find_entry_for_goal ~undo (st:t) (goal:Term.t) : tbl_entry option =
    Vec.to_iter st.tbl
    |> Iter.find_map
      (fun entry ->
         (* use [entry] iff it matches [goal] *)
         let goal_entry = entry.e_goal in
         if Array.length goal_entry = 1 then (
           Undo_stack.with_ undo (fun () ->
             try
               Unif.match_ ~undo (Array.get goal_entry 0) goal;
               Some entry
             with Unif.Fail -> None)
         ) else None)

  (* choice of which rule to use for a tree:
     - if tree is root, look for resolution (recursive of not) OR solution
     - otherwise, look for non-rec/cheap-rec function for resolution, OR
       add-or-get table entry for rec function, OR solution
   *)

  type rule_to_apply =
    | RA_solution
    | RA_dead (* dead tree *)
    | RA_resolution of int * Fun.t * Rule.t list * Term.t (* direct resolution *)
    | RA_tabling of int * Term.t (* rec function to memoize *)

  exception Found_rule of rule_to_apply

  let find_rule_to_apply ~at_root (_st:t) (tree:tree) : rule_to_apply =
    let@() = Tracing.with_ "find-rule-to-apply" in
    let c = tree.t_clause in
    if is_solution_c c then RA_solution
    else (
      let to_memo = ref None in
      try
        Array.iteri
          (fun i t ->
             match Term.view t with
             | Term.Var _ -> assert false
             | Term.Eqn _ -> ()
             | Term.App {f; _} ->
               begin match Fun.kind f with
                 | F_defined def ->
                   if at_root || not def.recursive || true || def.n_rec_calls <= 1 then (
                     (* FIXME: when tabling works, restore this test
                        to only use resolution on not-too-recursive recfuns *)
                     (* resolution will not duplicate effort since the function
                        is not recursive, or calls itself at most once,
                        thus avoiding explosion of the search space *)
                     let ra = RA_resolution (i,f,def.rules,t) in
                     raise (Found_rule ra)
                   ) else if Option.is_none !to_memo then (
                     to_memo := Some (i,t) (* tabling on [t] if no resolution is found *)
                   )
                 | _ -> ()
               end)
          c.Clause.guard;
        (* resolution failed, see if tabling applies *)
        match !to_memo with
        | None -> RA_dead
        | Some (i,t) -> RA_tabling (i,t)
      with Found_rule r -> r
    )

  (* perform resolution *)
  let do_resolution ~undo:_ (st:t) (tree:tree) (i:int) f (rules:_ list) (t:Term.t) : unit =
    let c = tree.t_clause in
    Log.logf 4 (fun k->k "(@[@{<yellow>do_resolution@}@ :term %a@])" Term.pp t);
    let guard =
      let a = c.Clause.guard in
      Array.init (Array.length a-1)
        (fun j -> if j<i then Array.get a j else Array.get a (j+1))
    in
    tree.t_label <- L_program {term=t; fun_=f};
    let undo = Undo_stack.create() in
    List.iter
      (fun r ->
         Log.logf 5 (fun k->k "(@[do_resolution.step@ :rule %a@ :term %a@])" Rule.pp r Term.pp t);
         let c' =
           Undo_stack.with_ undo
             (fun () ->
                try
                  Unif.unify ~undo t (Rule.concl r);
                  let c' =
                    Clause.make c.Clause.concl (Array.append guard @@ Rule.body r)
                    |> Clause.deref_deep
                    |> Clause.rename
                  in
                  Some c'
                with Unif.Fail -> None)
         in
         match Option.flat_map (mk_tree ~kind:Tree_open tree.t_entry) c' with
         | None -> ()
         | Some tree' ->
           Log.logf 5 (fun k->k "(@[resolution-yields@ %a@])" Clause.pp tree'.t_clause);
           push_task st tree';
      )
      rules

  (* [tree] defers to another entry, see if some resolutions now apply,
     and fast-forward offset *)
  let fast_forward_resolution ~undo (st:t) (tree:tree) : unit =
    let c = tree.t_clause in
    match tree.t_label with
    | L_defer defer ->
      let solutions = defer.entry.e_solutions in
      let len = Vec.length solutions in
      Log.logf 5 (fun k->k "(@[fast-forward-res (%d times)@ %a@ :to-goal (@[%a@])@])"
          (len-defer.offset) pp_tree tree (pp_array Term.pp) defer.entry.e_goal);
      (* guard of [c], minus the goal to resolve against the other entry *)
      let guard_c =
        let g = c.Clause.guard in
        Array.init (Array.length g-1)
          (fun j -> if j<defer.goal_idx then Array.get g j else Array.get g (j+1))
      in
      for i = defer.offset to len - 1 do
        let sol = Vec.get solutions i in
        Log.logf 5 (fun k->k "(@[resolved-against-solution@ :goal %a@ :sol %a@])"
            Term.pp defer.goal Clause.pp sol);
        let c' =
          if Array.length sol.Clause.concl <> 1 then None
          else
            Undo_stack.with_ undo (fun () ->
               try
                 Unif.unify ~undo defer.goal (Array.get sol.Clause.concl 0);
                 let c' =
                   Clause.make c.Clause.concl (Array.append guard_c @@ sol.Clause.guard)
                   |> Clause.deref_deep
                   |> Clause.rename
                 in
                 Some c'
               with Unif.Fail -> None)
        in
        match Option.flat_map (mk_tree ~kind:Tree_open tree.t_entry) c' with
        | None -> ()
        | Some tree' ->
          Log.logf 5 (fun k->k "(@[resolution-yields@ %a@])" Clause.pp tree'.t_clause);
          push_task st tree';
      done;
      defer.offset <- len-1;
    | _ -> assert false

  (* defer [tree] to some new or existing entry for subogal [t] *)
  let do_tabling ~undo (st:t) (tree:tree) (i:int) (t:Term.t) : unit =
    let@ () = Tracing.with_ "do-tabling" in
    Log.logf 4 (fun k->k "(@[@{<yellow>do_tabling@}@ :term %a@])" Term.pp t);
    (* look if there's an existing entry for this subgoal *)
    begin match find_entry_for_goal ~undo st t with
      | Some entry ->
        Log.logf 4 (fun k->k "(@[@{<yellow>defer_to_existing@}@ %a@])" (pp_array Term.pp) entry.e_goal);
        Vec.push entry.e_listeners tree;
        tree.t_label <- L_defer {entry; goal=t; goal_idx=i; offset=0;};
        (* do resolution right now, in case [entry] has solutions *)
        if not @@ Vec.is_empty entry.e_solutions then (
          fast_forward_resolution ~undo st tree;
        )
      | None ->
        Log.logf 4 (fun k->k "(@[@{<yellow>make_new_entry@}@])");
        let ta = [| t |] in
        let c' = Clause.make ta ta |> Clause.rename in
        let entry = mk_entry ta in
        (* see if the original clause is not absurd *)
        begin match mk_tree ~kind:Tree_root entry c' with
          | None ->
            Log.log 5 "(tree-is-dead)";
            tree.t_kind <- Tree_dead;
          | Some tree' ->
            Log.logf 5 (fun k->k "(@[new-entry-with@ %a@])" pp_tree tree');
            (* now we need to process [tree'] *)
            push_task st tree';
            Vec.push st.tbl entry;
            (* defer [tree] to [entry], which has no solutions yet *)
            tree.t_label <- L_defer {entry; goal=t; goal_idx=i; offset=0};
        end;
    end

  let apply_rule ~undo (st:t) (tree:tree) (ra:rule_to_apply) : unit =
    assert (tree.t_label = L_none);
    begin match ra with
      | RA_dead -> tree.t_kind <- Tree_dead
      | RA_solution ->
        Log.logf 5 (fun k->k "(@[@{<yellow>tree.is_solution@}@ %a@])" pp_tree tree);
        (* add to solutions *)
        tree.t_label <- L_solution;
        Vec.push tree.t_entry.e_solutions tree.t_clause;
        (* notify listeners *)
        Vec.iter (push_task st) tree.t_entry.e_listeners;
        ()
      | RA_resolution (i,f,rules,t) ->
        do_resolution ~undo st tree i f rules t
      | RA_tabling (i,t) ->
        do_tabling ~undo st tree i t
    end

  (* Label a single tree. We assume that the clause is simplified already. *)
  let process_tree (st:t) (tree:tree) : unit =
    let@ () = Tracing.with_ "process-tree" in
    Log.logf 2 (fun k->k "(@[@{<yellow>process_tree@}@ :n-steps %d@ %a@])" st.n_steps pp_tree tree);
    let undo = Undo_stack.create() in
    begin match tree.t_kind, tree.t_label with
      | Tree_dead, _ -> ()
      | Tree_open, L_none ->
        let rule = find_rule_to_apply ~at_root:false st tree in
        apply_rule ~undo st tree rule
      | Tree_root, L_none ->
        let rule = find_rule_to_apply ~at_root:true st tree in
        apply_rule ~undo st tree rule
      | _, L_defer _ ->
        (* defer to another entry which got new solutions *)
        fast_forward_resolution ~undo st tree
      | _, (L_program _ | L_solution) -> assert false (* should not process again *)
    end

  (* process tasks until we find a new solution *)
  let next_ (st:t) : Clause.t option * _ =
    let@ () = Tracing.with_ "solver.next" in
    let n_sols0 = n_root_sols st in
    let old_steps = st.n_steps in
    while n_root_sols st = n_sols0 && has_task st do

      st.n_steps <- 1 + st.n_steps;
      Tracing.instant "step" ~args:["n", `Int st.n_steps];

      pp_progress st;
      let tree = next_task st in
      process_tree st tree
    done;
    Util.Status.flush();
    (* if new solution was found, return it *)
    let res =
      if n_root_sols st > n_sols0 then (
        Some (Vec.get st.root.e_solutions n_sols0)
      ) else None
    in
    res, st.n_steps - old_steps

  let sol_of_clause (s:t) (c:Clause.t) : Solution.t =
    let@() = Tracing.with_ "solver.sol-of-clause" in
    let goal = s.root.e_goal in
    let vars = Term.vars_iter (CCArray.to_iter goal) in
    let map =
      let undo = Undo_stack.create () in
      Undo_stack.with_ undo (fun () ->
        assert (Array.length goal = Array.length (Clause.concl c));
        try
          Array.iter2 (Unif.unify ~undo) goal (Clause.concl c);
          Var.Set.to_iter vars
          |> Iter.map (fun v -> v, Term.deref_deep (Term.var v))
          |> Var.Map.of_iter
        with Unif.Fail -> assert false)
    in
    {Solution.subst=map; constr=Array.to_list @@ Clause.guard c}

  (* convert a clause into a {!solution} *)
  let next_solution s : Solution.t option * _ =
    let r, n = next_ s in
    Option.map (sol_of_clause s) r, n

  (* make a new solver for the given goal *)
  let make ?(config=Config.default) (g:goal) : t =
    assert (g <> []);
    let g = Array.of_list g in
    let c = Clause.make g g in
    let entry = mk_entry g in
    let st = {
      tbl=Vec.return entry; config; root=entry; tasks=Queue.create();
      n_tasks=0; n_steps=0;
    } in
    (* see if the original clause is not absurd *)
    begin match mk_tree ~kind:Tree_root entry c with
      | None -> ()
      | Some tree ->
        push_task st tree (* need to process this new [tree] *)
    end;
    st
end

let solve ?config (g:goal) : Solution.t option * _ =
  let s = Solver.make ?config g in
  Solver.next_solution s

(**/**)
module Fmt = CCFormat
module Util = Util
(**/**)
