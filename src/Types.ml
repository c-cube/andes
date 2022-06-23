
(** {1 Terms} *)

open Util

type var = {
  v_id: ID.t;
  mutable v_binding: term option;
  mutable v_marked: bool; (* temporary *)
}

and term = {
  t_view: term_view;
  mutable t_ground: bool;
  mutable t_id: int;
}

and fun_ = {
  f_id: ID.t;
  f_arity: int;
  mutable f_kind: fun_kind;
}

and fun_kind =
  | F_cstor
  | F_defined of {
      mutable rules: rule list;
      recursive: bool;
      mutable n_rec_calls: int; (* number of recursive sub-calls *)
    }

(** Logic rule. Variables can be renamed in place when the rule is
    successfully applied. *)
and rule = {
  mutable rule_concl: term;
  mutable rule_body: term array;
}

and term_view =
  | Var of var
  | App of {
      f: fun_;
      args: term array;
    }
  | Eqn of {
      sign: bool;
      lhs: term;
      rhs: term;
    }

module Var = struct
  type t = var

  let[@inline] make s : t = {v_id=ID.make s; v_binding=None; v_marked=false;}
  let makef fmt = Fmt.ksprintf ~f:make fmt
  let[@inline] copy {v_id;_} : t = {v_id=ID.copy v_id; v_binding=None; v_marked=false}

  let fresh =
    let vars = "xyzuvw" in
    let n = ref 0 in
    fun () -> incr n;
      let d, q = !n mod (String.length vars), !n / String.length vars in
      makef "%c%s" vars.[d] (if q=0 then "" else string_of_int q)

  let[@inline] equal a b = ID.equal a.v_id b.v_id
  let[@inline] compare a b = ID.compare a.v_id b.v_id
  let[@inline] hash a = ID.hash a.v_id
  let pp out v = Fmt.fprintf out "?%a" ID.pp v.v_id

  let[@inline] marked v = v.v_marked
  let[@inline] mark v = v.v_marked <- true
  let[@inline] unmark v = v.v_marked <- false

  module Map = CCMap.Make(struct type nonrec t = t let compare = compare end)
  module Set = CCSet.Make(struct type nonrec t = t let compare = compare end)
end

module Fun = struct
  type t = fun_

  type kind = fun_kind =
    | F_cstor
    | F_defined of {
        mutable rules: rule list;
        recursive: bool;
        mutable n_rec_calls: int; (* number of recursive sub-calls *)
      }

  type rule_promise = t

  let is_defined f = match f.f_kind with F_defined _ -> true | _ -> false
  let is_recursive f = match f.f_kind with F_defined {recursive=b;_} -> b | _ -> false

  let mk_cstor id ~arity : t = {f_id=id; f_arity=arity; f_kind=F_cstor}
  let mk_defined id ~arity ~recursive : t * rule_promise =
    let f_kind = F_defined {rules=[];recursive; n_rec_calls=0} in
    let f = {f_id=id; f_arity=arity; f_kind} in
    f, f

  let[@inline] id f = f.f_id
  let[@inline] kind f = f.f_kind
  let[@inline] arity f = f.f_arity

  let[@inline] equal a b = ID.equal a.f_id b.f_id
  let[@inline] compare a b = ID.compare a.f_id b.f_id
  let[@inline] hash a = ID.hash a.f_id
  let pp out f = ID.pp out f.f_id
  let to_string f = ID.to_string f.f_id
end

(* used to quickly rename variables in a term/clause *)
module Renaming = struct
  type t = (Var.t * term option) Vec.vector (* restore binding + unmark *)

  let[@inline] create () = Vec.create()

  let finish (st:t) =
    Vec.iter (fun (v,bind) -> Var.unmark v; v.v_binding <- bind) st

  let with_ f =
    let r = create() in
    try
      let x = f r in
      finish r;
      x
    with e ->
      finish r;
      raise e
end


let rec pp_term_ out a : unit =
  match a.t_view with
  | Var v -> Var.pp out v
  | App {f; args=[||]} -> Fun.pp out f
  | App {f; args} ->
    Format.fprintf out "(@[%a@ %a@])" Fun.pp f (pp_array pp_term_) args
  | Eqn {sign;lhs;rhs} ->
    Format.fprintf out "(@[<hv>%s@ %a@ %a@])"
      (if sign then "=" else "!=") pp_term_ lhs pp_term_ rhs

module Subst = struct
  module M = Var.Map
  type t = term M.t

  let empty = M.empty
  let add self v t = M.add v t self
  let get self v = M.find_opt v self
  let mem self v = M.mem v self
  let to_iter = M.to_iter
  let pp out (self:t) =
    let pp_pair out (v,t) = Fmt.fprintf out "@ (@[%a %a@])" Var.pp v pp_term_ t in
    Fmt.fprintf out "(@[subst%a@])"
    (pp_iter pp_pair) (to_iter self)
end

module Term = struct
  type t = term

  type view = term_view =
    | Var of Var.t
    | App of {
        f: Fun.t;
        args: t array;
      }
    | Eqn of {
        sign: bool;
        lhs: t;
        rhs: t;
      }

  let[@inline] view (t:t) = t.t_view

  let[@inline] equal (a:t) (b:t) : bool = a == b

  let[@inline] compare (a:t) (b:t) : int = CCInt.compare a.t_id b.t_id

  let[@inline] hash (t:t) : int = CCHash.int t.t_id

  let[@inline] is_ground t = t.t_ground

  module As_key = struct
    type t = term
    let hash = hash
    let equal = equal
    let compare = compare
  end
  module Tbl = CCHashtbl.Make(As_key)
  module Set = CCSet.Make(As_key)

  module H = Hashcons.Make(struct
    type t = term

    let set_id t id =
      assert (t.t_id = -1);
      t.t_id <- id

    let equal t1 t2 = match t1.t_view, t2.t_view with
    | Var v1, Var v2 -> Var.equal v1 v2
    | App a1, App a2 -> Fun.equal a1.f a2.f && CCArray.equal equal a1.args a2.args
    | Eqn e1, Eqn e2 ->
        e1.sign = e2.sign &&
        equal e1.lhs e2.lhs &&
        equal e1.rhs e2.rhs
    | (Var _ | App _ | Eqn _), _ -> false

    let hash a : int =
      match view a with
      | Var v -> CCHash.combine2 10 (Var.hash v)
      | App {f; args} ->
        CCHash.combine3 20 (Fun.hash f) (CCHash.iter hash @@ CCArray.to_iter args)
      | Eqn { sign; lhs; rhs } ->
        CCHash.combine4 30 (CCHash.bool sign) (hash lhs) (hash rhs)
  end)

  let pp = pp_term_

  let tbl_ = H.create()

  (* term builder *)
  let mk_ : view -> t =
    fun (t_view:view) : t ->
      let t = {t_view; t_id= -1; t_ground=true} in
      let u = H.hashcons tbl_ t in
      if t == u then (
        (* new term, compute cached properties *)
        let ground = match t_view with
          | Var _ -> false
          | App {f=_; args} -> Array.for_all is_ground args
          | Eqn {lhs; rhs; sign=_} -> is_ground lhs && is_ground rhs
        in
        u.t_ground <- ground;
      );
      u

  let[@inline] var v : t = mk_ @@ Var v

  let app f args : t =
    if Fun.arity f <> Array.length args then (
      Util.errorf "cannot apply %a (arity %d)@ to [@[%a@]]"
        Fun.pp f (Fun.arity f) (Util.pp_array pp) args
    );
    mk_ @@ App {f;args}

  let app_l f args : t = app f (Array.of_list args)
  let const f : t = app f [||]
  let eqn ~sign lhs rhs =
    (* normalize *)
    let lhs, rhs = if compare lhs rhs <= 0 then lhs, rhs else rhs, lhs in
    mk_ @@ Eqn {lhs; rhs; sign}

  let eq a b : t = eqn ~sign:true a b
  let neq a b : t = eqn ~sign:false a b

  let is_var t = match view t with Var _ -> true | _ -> false
  let as_var_exn t = match view t with Var v -> v | _ -> assert false

  let[@unroll 2] rec deref (t:t) : t =
    match view t with
    | Var {v_binding=Some u;_} -> deref u
    | _ -> t

  (* shallow deref *)
  let deref_var subst (t:term) : term =
    let rec aux t =
      if is_ground t then t (* shortcut *)
      else
        match view t with
        | Var v ->
            begin match Subst.get subst v with
            | None -> t
            | Some u -> aux u
            end
        | App _ | Eqn _ -> t
    in aux t

  let subterms ?(tbl=Tbl.create 8) ?(enter=fun _ -> true) t yield : unit =
    let rec aux t =
      let t = deref t in
      if not (Tbl.mem tbl t) then (
        Tbl.add tbl t ();
        yield t;
        if enter t then (
          match view t with
          | Var _ -> ()
          | App {args;_} -> Array.iter aux args
          | Eqn {lhs;rhs;_} -> aux lhs; aux rhs
        )
      )
    in
    aux t

  let contains_var ?tbl v t : bool =
    subterms t ?tbl ~enter:(fun t -> not (is_ground t))
    |> Iter.exists
    (fun t ->
      match view t with
      | Var u -> Var.equal v u
      | _ -> false)

  let vars_of_iter_ it : Var.Set.t =
    it
    |> Iter.filter_map
      (fun t -> match view t with
         | Var v -> Some v
         | _ -> None)
    |> Var.Set.of_iter

  let vars_iter ?(tbl=Tbl.create 8) (it:t Iter.t) : Var.Set.t =
    it
    |> Iter.flat_map (fun t -> subterms t ~tbl ~enter:(fun t -> not (is_ground t)))
    |> vars_of_iter_

  let vars ?tbl t = vars_of_iter_ @@ subterms ?tbl t

  (* map superterms, then subterms.
     Only enter subterm [t] if [enter t] is true *)
  let map_top_down_
      ?(cache=Tbl.create 8)
      ?(enter=fun _ -> true) ~recursive ~(f:t -> t option) (t0:t) : t =
    let rec loop t =
      match Tbl.find_opt cache t with
      | Some u -> u
      | None ->
        let res =
          match f t with
          | Some u when recursive -> loop u
          | Some u -> u
          | None ->
            match view t with
            | Var _ | App {args=[||]; _} -> t
            | _ when not (enter t) -> t
            | App {f; args} ->
              let args' = Array.map loop args in
              if CCArray.equal (==) args args' then t else app f args'
            | Eqn {sign;lhs;rhs} ->
              let lhs' = loop lhs in
              let rhs' = loop rhs in
              if lhs==lhs' && rhs==rhs' then t else eqn ~sign lhs' rhs'
        in
        Tbl.add cache t res;
        res
    in
    loop t0

  (* follow variable bindings deeply *)
  let deref_deep ?cache t =
    map_top_down_ ?cache ~recursive:true t
     ~enter:(fun t -> not (is_ground t))
     ~f:(fun t -> match view t with
        | Var {v_binding=Some u;_} -> Some u
        | _ -> None)

  (* apply substitution *)
  let apply_subst ?cache subst t =
    map_top_down_ ?cache ~recursive:true t
     ~enter:(fun t -> not (is_ground t))
     ~f:(fun t -> match view t with
        | Var v -> Subst.get subst v
        | _ -> None)

  let rename ?cache (ren:Renaming.t) (t: term) : term =
    map_top_down_ ?cache ~recursive:false t
      ~enter:(fun t -> not (is_ground t))
      ~f:(fun t ->
        match view t with
        | Var ({v_binding=Some u; _} as v) when Var.marked v ->
          Some u (* follow renaming *)
        | Var v ->
          (* [v] is not bound, rename it to [v'] *)
          let v' = Var.copy v in
          Var.mark v;
          Vec.push ren (v, v.v_binding);
          let u = var v' in
          v.v_binding <- Some u;
          Some u
        | _ -> None)

  let rename_arr ?(cache=Tbl.create 8) r a = Array.map (rename ~cache r) a
end

module Clause = struct
  type t = {
    concl: Term.t array; (* non empty *)
    guard: Term.t array;
  }

  let[@inline] concl c = c.concl
  let[@inline] guard c = c.guard

  let map f c =
    {concl=Array.map f c.concl;
     guard=Array.map f c.guard;
    }

  let apply_subst ?(cache=Term.Tbl.create 8) subst self =
    map (Term.apply_subst ~cache subst) self

  let rename ?(cache=Term.Tbl.create 8) c =
    Renaming.with_ (fun ren -> map (Term.rename ~cache ren) c)

  let deref_deep ?cache c = map (Term.deref_deep ?cache) c

  let[@inline] equal a b : bool =
    CCArray.equal Term.equal a.concl b.concl &&
    CCArray.equal Term.equal a.guard b.guard

  let[@inline] make a b : t = {concl=a; guard=b}

  let pp out (c:t) =
    let pp_iarray_b out a =
      if a  = [||] then Fmt.string out "()"
      else if Array.length a =1 then Term.pp out (Array.get a 0)
      else Fmt.fprintf out "(@[<hv>%a@])" (pp_array Term.pp) a
    in
    Fmt.fprintf out "(@[%a@ <- %a@])" pp_iarray_b c.concl pp_iarray_b c.guard
end

module Rule = struct
  type t = rule

  let concl r = r.rule_concl
  let body r = r.rule_body
  let equal a b : bool =
    Term.equal (concl a) (concl b) && CCArray.equal Term.equal (body a) (body b)

  let to_clause r = Clause.make [| concl r |] (body r)
  let head r = match Term.view @@ concl r with
    | Term.App {f; _} -> f
    | _ -> Util.errorf "rule.head"

  let rename_in_place r : unit =
    let@ () = Tracing.with_ "rule.rename" ~args:["body.len", `Int (Array.length r.rule_body)] in
    Renaming.with_
      (fun ren ->
         let cache = Term.Tbl.create 8 in
         r.rule_concl <- Term.rename ~cache ren r.rule_concl;
         r.rule_body <- Term.rename_arr ~cache ren r.rule_body)

  let make concl body : t =
    begin match Term.view concl with
      | Term.App {f; _} when Fun.is_defined f ->  ()
      | _ ->
        Util.errorf "rule cannot have head %a,@ expect defined function" Term.pp concl
    end;
    let r = { rule_concl=concl; rule_body=body } in
    rename_in_place r;
    r

  let make_l concl body = make concl (Array.of_list body)

  let pp out (r:t) =
    let pp_body out b =
      if array_is_empty b then Fmt.fprintf out "."
      else Fmt.fprintf out " :-@ %a." (pp_array Term.pp) b
    in
    Format.fprintf out "(@[<hv>%a%a@])" Term.pp (concl r) pp_body (body r)

  let add_to_def ?(n_rec_calls=0) (f:Fun.rule_promise) (l:t list) =
    match Fun.kind f with
    | Fun.F_defined def ->
      assert (def.rules = []);
      (* is there a rule that doesn't have [add] as head symbol? *)
      let bad_r =
        CCList.find_pred
          (fun r -> match Term.view r.rule_concl with App a -> not @@ Fun.equal a.f f | _ -> true) l
      in
      begin match bad_r with
        | None ->  ()
        | Some r -> Util.errorf "rule %a@ cannot be added to %a" pp r Fun.pp f
      end;
      Log.logf 3
        (fun k->k "(@[rule.add_to_def@ :fun %a@ :n-rec-calls %d@ :rules [@[<v>%a@]]@])"
            Fun.pp f n_rec_calls (Util.pp_list pp) l);
      def.rules <- l;
      def.n_rec_calls <- n_rec_calls;
    | _ -> assert false
end

module Unif = struct
  exception Fail

  type op = O_unif | O_match

  module Tbl2 = CCHashtbl.Make(struct
    type t = Term.t * Term.t
    let equal = CCEqual.pair Term.equal Term.equal
    let hash = CCHash.pair Term.hash Term.hash
  end)

  let occurs_check subst v t : bool =
    assert (v.v_binding = None);
    let rec aux t =
      let t = Term.deref_var subst t in
      if Term.is_ground t then false (* shortcut *)
      else
        match Term.view t with
        | Var v' ->
          Var.equal v v'
        | App {args; f=_} -> Array.exists aux args
        | Eqn {lhs; rhs; sign=_} -> aux lhs || aux rhs
    in aux t

  let[@inline] can_bind subst v t = not (occurs_check subst v t)

  let unif_ op subst a b : Subst.t =
    let tbl = Tbl2.create 8 in
    let subst = ref subst in
    let rec aux a b =
      let a = Term.deref_var !subst a in
      let b = Term.deref_var !subst b in
      if Tbl2.mem tbl (a,b) then ()
      else (
        Tbl2.add tbl (a,b) (); (* unify pair [a,b] once per pair at most *)
        match Term.view a, Term.view b with
        | Var v1, Var v2 when Var.equal v1 v2 -> ()
        | Var v, _ ->
          if occurs_check !subst v b then raise Fail;
          subst := Subst.add !subst v b
        | _, Var v when (match op with O_unif -> true | O_match -> false) ->
          (* can bind var on the RHS, if we're doing full unif and not just matching *)
          if occurs_check !subst v a then raise Fail;
          subst := Subst.add !subst v a
        | App r1, App r2
          when Fun.equal r1.f r2.f && Array.length r1.args = Array.length r2.args ->
          Array.iter2 aux r1.args r2.args
        | Eqn r1, Eqn r2 when r1.sign = r2.sign ->
          aux r1.lhs r2.lhs;
          aux r1.rhs r2.rhs;
        | App _, _ | Eqn _, _ -> raise Fail;
      )
    in
    aux a b;
    !subst

  let unify s a b = unif_ O_unif s a b
  let match_ s a b = unif_ O_match s a b
end

