
open Types
open Util

exception Several_rules
exception Simp_absurd

(* simplify the clause at this tree until either:
   - the clause is found to be absurd (impossible guard)
   - each term in the guard is maximally simplified and has several
   rules that can potentially apply;
   or, for constraints, the conjunction of constraints is SAT
*)
let simplify_ (c:Clause.t) : Clause.t option =
  let undo = Undo_stack.create() in
  let idx = ref 0 in
  let vec = Vec.of_array (IArray.to_array_copy c.Clause.guard) in
  let restart () : unit =
    Log.log 5 "(simplify.restart)";
    idx := 0
  in
  let absurd (t:Term.t) : 'a =
    Log.logf 5 (fun k->k "(@[simplify.is_absurd@ %a@])" Term.pp t);
    raise_notrace Simp_absurd
  in
  (* simplify given term, pushing it to [new_guard] if not simplifiable,
     or pushing new terms to simplify to [to_process].
     If term is absurd, raise Simp_absurd. *)
  let simp_t (t:Term.t) : unit = match Term.view t with
    | Term.Var _ -> assert false (* not at toplevel *)
    | Term.Eqn {sign=true; lhs; rhs} when Term.is_var lhs || Term.is_var rhs ->
      (* [x=t] replaces [x] with [t] everywhere, of fails by occur check.
         if binding succeeds, need to re-simplify again *)
      let save = Undo_stack.save undo in
      begin match Unif.unify ~undo lhs rhs with
        | () ->
          Log.logf 5 (fun k->k "(@[simplify.eq-res@ %a@])" Term.pp t);
          Vec.remove vec !idx;
          restart();
        | exception Unif.Fail ->
          Undo_stack.restore undo save;
          absurd t
      end
    | Term.Eqn {sign=false; lhs; rhs} when Term.equal lhs rhs ->
      absurd t (* [t!=t] absurd *)
    | Term.Eqn {sign=false; lhs; rhs} ->
      Undo_stack.with_ ~undo (fun undo ->
        try
          Unif.unify ~undo lhs rhs;
          incr idx;
        with Unif.Fail ->
          (* never equal, drop *)
          Log.logf 5 (fun k->k "(@[simplify.trivial-neq@ %a@])" Term.pp t);
          Vec.remove vec !idx;
      )
    | Term.Eqn {sign=true; lhs; rhs} ->
      (* check that [lhs] and [rhs] are unifiable, if yes keep them *)
      Undo_stack.with_ ~undo (fun undo ->
        try Unif.unify ~undo lhs rhs
        with Unif.Fail -> absurd t);
      Vec.remove vec !idx;
    | Term.App {f; _} ->
      begin match Fun.kind f with
        | Fun.F_cstor -> incr idx
        | Fun.F_defined {rules=[]} -> incr idx (* not defined yet *)
        | Fun.F_defined {rules} ->
          (* try to apply the rules, and simplify if zero or one apply *)
          let n_success = ref 0 in
          begin match
              CCList.filter_map
                (fun r ->
                   Undo_stack.with_ ~undo
                     (fun undo ->
                        try
                          (* keep rule if its conclusion unifies with [t] *)
                          Unif.unify ~undo (Rule.concl r) t;
                          if !n_success > 0 then raise_notrace Several_rules;
                          incr n_success;
                          Some r
                        with Unif.Fail -> None))
                rules
            with
            | [] -> absurd t
            | [rule] ->
              (* exactly one rule applies, so resolve with its unconditionally *)
              Log.logf 5 (fun k->k "(@[simplify.uniq-rule@ :goal %a@ :rule %a@])"
                  Term.pp t Rule.pp rule);
              Unif.unify ~undo (Rule.concl rule) t;
              let rule_body = Rule.body rule |> IArray.map Term.deref_deep in
              (* remove lit, push guard *)
              Vec.remove vec !idx;
              IArray.iter (Vec.push vec) rule_body;
              restart();
              Rule.rename_in_place rule; (* consume rule's current version *)
            | exception Several_rules ->
              (* several rules, keep *)
              incr idx
            | _::_::_ -> assert false
          end
      end
  in
  (* simplification fixpoint *)
  try
    while !idx < Vec.length vec do
      let t = Vec.get vec !idx in
      Log.logf 5 (fun k->k "(@[simplify.process@ %a@])" Term.pp t);
      simp_t t
    done;
    let c' =
      Clause.make c.Clause.concl (Vec.to_array vec |> IArray.of_array_unsafe)
      |> Clause.deref_deep
    in
    if not @@ Clause.equal c c' then (
      Log.logf 3
        (fun k->k "(@[@{<green>simplify.done@}@ :from %a@ :into %a@])" Clause.pp c Clause.pp c');
    );
    Some c'
  with Simp_absurd ->
    Log.logf 3 (fun k->k "(@[simplify.absurd@ %a@])" Clause.pp c);
    None

let simplify_c c : _ option =
  Util.Status.print "simplify clause";
  simplify_ c

let simplify_rule (r:Rule.t) : Rule.t option =
  Util.Status.printf "simplify rule for %s" (Fun.to_string @@ Rule.head r);
  let c = Rule.to_clause r in
  match simplify_ c with
  | None -> None
  | Some c ->
    assert (IArray.length c.Clause.concl = 1);
    let r = Rule.make (IArray.get c.Clause.concl 0) c.Clause.guard in
    Some r

