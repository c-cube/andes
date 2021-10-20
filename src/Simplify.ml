
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
  let concl = ref c.Clause.concl in
  let to_process = Vec.of_array (IArray.to_array_copy c.Clause.guard) in
  let new_guard = Vec.create () in
  let pp_state out () =
    Fmt.fprintf out "(@[:to_process (@[%a@])@ :new_guard (@[%a@])@])"
      (Vec.pp Term.pp) to_process (Vec.pp Term.pp) new_guard
  in
  (* after some variable has been bound, re-simplify
     terms that can be simplified *)
  let restart () : unit =
    Log.log 5 "(simplify.restart)";
    concl := IArray.map Term.deref_deep !concl;
    Vec.iteri (fun i t -> Vec.set to_process i (Term.deref_deep t)) to_process;
    Vec.filter_in_place
      (fun t ->
         let t' = Term.deref_deep t in
         if Term.equal t t' then true
         else (
           Vec.push to_process t';
           false
         ))
      new_guard;
    Log.logf 10 (fun k->k "(@[simplify.restart@ :yields %a@])" pp_state());
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
      (* FIXME: should we simplify even for non-vars? *)
      (* [x=t] replaces [x] with [t] everywhere, of fails by occur check.
         if binding succeeds, need to re-simplify again *)
      Undo_stack.with_ ~undo (fun undo ->
        try
          Unif.unify ~undo lhs rhs;
          Log.logf 5 (fun k->k "(@[simplify.eq-res@ %a@])" Term.pp t);
          restart();
        with Unif.Fail ->
          absurd t)
    | Term.Eqn {sign=false; lhs; rhs} when Term.equal lhs rhs ->
      absurd t (* [t!=t] absurd *)
    | Term.Eqn {sign=false; lhs; rhs} ->
      Undo_stack.with_ ~undo (fun undo ->
        try
          Unif.unify ~undo lhs rhs;
          Vec.push new_guard t (* keep *)
        with Unif.Fail ->
          (* never equal, drop *)
          Log.logf 5 (fun k->k "(@[simplify.trivial-neq@ %a@])" Term.pp t);
      )
    | Term.Eqn {sign=true; lhs; rhs} ->
      (* check that [lhs] and [rhs] are unifiable, if yes keep them *)
      Undo_stack.with_ ~undo (fun undo ->
        try Unif.unify ~undo lhs rhs
        with Unif.Fail -> absurd t);
      Vec.push new_guard t
    | Term.App {f; _} ->
      begin match Fun.kind f with
        | Fun.F_cstor -> Vec.push new_guard t
        | Fun.F_defined {rules=[]; _} -> Vec.push new_guard t (* not defined yet *)
        | Fun.F_defined {rules; _} ->
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
              Undo_stack.with_ ~undo (fun undo ->
                Unif.unify ~undo (Rule.concl rule) t;
                let rule_body = Rule.body rule |> IArray.map Term.deref_deep in
                IArray.iter (Vec.push to_process) rule_body;
                restart());
              Rule.rename_in_place rule; (* consume rule's current version *)
            | exception Several_rules ->
              (* several rules, keep *)
              Vec.push new_guard t
            | _::_::_ -> assert false
          end
      end
  in
  (* simplification fixpoint *)
  try
    while not @@ Vec.is_empty to_process do
      let t = Vec.pop_exn to_process in
      Log.logf 5 (fun k->k "(@[simplify.process@ %a@])" Term.pp t);
      simp_t t
    done;
    let c' =
      Clause.make !concl (Vec.to_array new_guard |> IArray.of_array_unsafe)
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

