
open Types
open Util

exception Simp_absurd

(* simplify the clause at this tree until either:
   - the clause is found to be absurd (impossible guard)
   - each term in the guard is maximally simplified and has several
     rules that can potentially apply;
   - or, for constraints, the conjunction of constraints is SAT
*)
let simplify_ (c:Clause.t) : Clause.t option =
  let to_process = Vec.of_array c.Clause.guard in
  let new_guard = ref Term.Set.empty in

  let subst = ref Subst.empty in

  let pp_state out () =
    Fmt.fprintf out "(@[:to_process (@[%a@])@ :new_guard (@[%a@])@ :subst %a@])"
      (Vec.pp Term.pp) to_process (pp_iter Term.pp) (Term.Set.to_iter !new_guard)
      Subst.pp !subst
  in

  let reprocess_if_contains v =
    let@() = Tracing.with_ "reprocess-if-contains" in
    let tbl = Term.Tbl.create 8 in
    new_guard :=
      Term.Set.filter
        (fun t ->
          if Term.contains_var ~tbl v t then (
            (* [t] is modified by the binding of [v] *)
            Vec.push to_process t;
            false
          ) else true)
      !new_guard;
  in

  let keep t =
    (*
    let t = Term.apply_subst !subst t in
    *)
    new_guard := Term.Set.add t !new_guard
  in

  let absurd (t:Term.t) : 'a =
    Log.logf 5 (fun k->k "(@[simplify.is_absurd@ %a@])" Term.pp t);
    raise_notrace Simp_absurd
  in

  (* after some variables has been bound, re-simplify
     terms that can be simplified *)
  let restart () : unit =
    let@() = Tracing.with_ "restart" in
    Log.log 5 "(simplify.restart)";
    (* check if some processed terms need to be re-processed *)
    new_guard :=
      Term.Set.filter
        (fun t ->
           let t' = Term.apply_subst !subst t in
           if Term.equal t t' then true
           else (
             Vec.push to_process t';
             false
           ))
      !new_guard;
    Log.logf 10 (fun k->k "(@[simplify.restart@ :yields %a@])" pp_state());
  in

  let need_restart = ref false in

  (* simplify given term, pushing it to [new_guard] if not simplifiable,
     or pushing new terms to simplify to [to_process].
     If term is absurd, raise Simp_absurd. *)
  let simp_t (t:Term.t) : unit =
    match Term.view t with
    | Term.Var _ -> assert false (* not at toplevel *)
    | Term.Eqn {sign=true; lhs; rhs} ->

      let@ () = Tracing.with_ "simp.eqn" in
      let lhs = Term.deref_var !subst lhs in
      let rhs = Term.deref_var !subst rhs in

      (match Term.view lhs, Term.view rhs with
      | Var v, _ when Unif.can_bind !subst v rhs ->
        Log.logf 5 (fun k->k "(@[simplify.eq-res@ %a@])" Term.pp t);
        subst := Subst.add !subst v rhs;
        reprocess_if_contains v

      | _, Var v when Unif.can_bind !subst v lhs ->
        Log.logf 5 (fun k->k "(@[simplify.eq-res@ %a@])" Term.pp t);
        subst := Subst.add !subst v lhs;
        reprocess_if_contains v
      | _ ->
        (* check that [lhs] and [rhs] are unifiable, if yes keep them.
           otherwise, keep the equation, but don't keep the unifier. *)
        (match Unif.unify !subst lhs rhs with
        | _ -> keep t
        | exception Unif.Fail -> absurd t)
      )

    | Term.Eqn {sign=false; lhs; rhs} when Term.equal lhs rhs ->
      absurd t (* [t!=t] absurd *)

    | Term.Eqn {sign=false; lhs; rhs} ->

      (match Unif.unify !subst lhs rhs with
      | _ -> keep t
      | exception Unif.Fail ->
          (* never equal, drop trivial constraint *)
        Log.logf 5 (fun k->k "(@[simplify.trivial-neq@ %a@])" Term.pp t);
      )

    | Term.App {f; _} ->
      begin match Fun.kind f with
        | Fun.F_cstor -> keep t
        | Fun.F_defined {rules=[]; _} -> keep t (* not defined yet *)
        | Fun.F_defined {rules; _} ->

          let@ () = Tracing.with_ "simp.defined-app" in

          (* try to apply the rules, and simplify if zero or one apply *)
          begin match
              CCList.filter_map
                (fun r ->
                  (* keep rule if its conclusion unifies with [t] *)
                  match Unif.unify !subst (Rule.concl r) t with
                  | subst -> Some (r, subst)
                  | exception Unif.Fail -> None)
                rules
            with
            | [] -> absurd t
            | [rule, subst'] ->
              (* exactly one rule applies, so resolve with its unconditionally *)
              Log.logf 5 (fun k->k "(@[simplify.uniq-rule@ :goal %a@ :rule %a@])"
                  Term.pp t Rule.pp rule);

              subst := subst';

              (* add body of rule to the literals to process *)
              Array.iter
                (Vec.push to_process)
                (Rule.body rule);

              need_restart := true;

              Rule.rename_in_place rule; (* consume rule's current version *)

            | _::_::_ ->
              (* several rules, don't simplify.
                 Will be dealt with in {!Andes}. *)
              keep t
          end
      end
  in
  (* simplification fixpoint *)
  try
    while not @@ Vec.is_empty to_process do
      while not @@ Vec.is_empty to_process do
        let t = Vec.pop_exn to_process in
        Log.logf 5 (fun k->k "(@[simplify.process@ %a@])" Term.pp t);
        simp_t t
      done;

      if !need_restart then (
        need_restart := false;
        restart(); (* might push things back into [to_process] *)
      )
    done;

    let c' =
      (* change guard, apply whole substitution.
         substitute in guard as a set so it deduplicates. *)
      let cache = Term.Tbl.create 8 in
      let guard =
        !new_guard
        |> Term.Set.map (Term.apply_subst ~cache !subst)
        |> Term.Set.to_iter |> Iter.to_array
      in
      Clause.make c.concl guard
      |> Clause.apply_subst !subst
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
  let@ () = Tracing.with_ "simplify-c" in
  Util.Status.print "simplify clause";
  simplify_ c

let simplify_rule (r:Rule.t) : Rule.t option =
  let@ () = Tracing.with_ "simplify-rule" in
  Util.Status.printf "simplify rule for %s" (Fun.to_string @@ Rule.head r);
  let c = Rule.to_clause r in
  match simplify_ c with
  | None -> None
  | Some c ->
    assert (Array.length c.Clause.concl = 1);
    let r = Rule.make (Array.get c.Clause.concl 0) c.Clause.guard in
    Some r

