
(** {1 Terms} *)

open Util

type var = {
  v_id: ID.t;
  mutable v_binding: term option;
  mutable v_marked: bool; (* temporary *)
}

and term = term_view

and fun_ = {
  f_id: ID.t;
  f_arity: int;
  mutable f_kind: fun_kind;
}

and fun_kind =
  | F_cstor
  | F_defined of {
      mutable rules: rule list;
    }

(** Logic rule. Variables can be renamed in place when the rule is
    successfully applied. *)
and rule = {
  mutable rule_concl: term;
  mutable rule_body: term IArray.t;
}

and term_view =
  | Var of var
  | App of {
      f: fun_;
      args: term IArray.t;
    }
  | Eqn of {
      sign: bool;
      lhs: term;
      rhs: term;
    }

module Var = struct
  type t = var

  let[@inline] make s : t = {v_id=ID.make s; v_binding=None; v_marked=false;}
  let[@inline] copy {v_id;_} : t = {v_id=ID.copy v_id; v_binding=None; v_marked=false}
  let fresh () = make "_"

  let[@inline] equal a b = ID.equal a.v_id b.v_id
  let[@inline] compare a b = ID.compare a.v_id b.v_id
  let[@inline] hash a = ID.hash a.v_id
  let pp out v = ID.pp out v.v_id

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
      }

  let mk_cstor id ~arity : t = {f_id=id; f_arity=arity; f_kind=F_cstor}
  let mk_defined id ~arity : t = {f_id=id; f_arity=arity; f_kind=F_defined {rules=[]}}

  let[@inline] kind f = f.f_kind
  let[@inline] equal a b = ID.equal a.f_id b.f_id
  let[@inline] compare a b = ID.compare a.f_id b.f_id
  let[@inline] hash a = ID.hash a.f_id
  let pp out v = ID.pp out v.f_id
end

module Renaming = struct
  type t = Var.t Vec.vector

  let create () = Vec.create ()

  let finish (st:t) = Vec.iter (fun v -> Var.unmark v; v.v_binding <- None) st

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

module Term = struct
  type t = term

  type view = term_view =
    | Var of Var.t
    | App of {
        f: Fun.t;
        args: t IArray.t;
      }
    | Eqn of {
        sign: bool;
        lhs: t;
        rhs: t;
      }

  let[@inline] view t = t

  let rec compare a b : int =
    let open CCOrd.Infix in
    let[@inline] to_int = function
      | Var _ -> 0
      | App _ -> 1
      | Eqn _ -> 2
    in
    match view a, view b with
    | _ when a==b -> 0 (* physically equal *)
    | Var a, Var b -> Var.compare a b
    | App a, App b ->
      let c = Fun.compare a.f b.f in
      if c<>0 then c else IArray.compare compare a.args b.args
    | Eqn a, Eqn b ->
      compare a.lhs b.lhs
      <?> (compare, a.rhs, b.rhs)
      <?> (CCOrd.bool, a.sign, b.sign)
    | Var _, _ | App _, _ | Eqn _, _ -> CCOrd.int (to_int @@ view a) (to_int @@ view b)

  let[@inline] equal a b = a==b || compare a b = 0

  let rec hash a : int =
    match view a with
    | Var v -> CCHash.combine2 10 (Var.hash v)
    | App {f; args} ->
      CCHash.combine3 20 (Fun.hash f) (CCHash.seq hash @@ IArray.to_seq args)
    | Eqn { sign; lhs; rhs } ->
      CCHash.combine4 30 (CCHash.bool sign) (hash lhs) (hash rhs)

  let rec pp out a : unit =
    match view a with
    | Var v -> Var.pp out v
    | App {f; args} when IArray.is_empty args -> Fun.pp out f
    | App {f; args} ->
      Format.fprintf out "(@[%a@ %a@])" Fun.pp f (pp_iarray pp) args
    | Eqn {sign;lhs;rhs} ->
      Format.fprintf out "(@[%s@ %a@ %a@])"
        (if sign then "=" else "!=") pp lhs pp rhs

  (* term builder *)
  let mk_ : view -> t =
    fun[@inline] t_view -> t_view

  let var v : t = mk_ @@ Var v
  let app f args : t = mk_ @@ App {f;args}
  let app_l f args : t = app f (IArray.of_list args)
  let const f : t = app f IArray.empty
  let eqn ~sign lhs rhs = mk_ @@ Eqn {lhs; rhs; sign}
  let eq a b : t = eqn ~sign:true a b
  let neq a b : t = eqn ~sign:false a b

  let is_var t = match view t with Var _ -> true | _ -> false

  let[@unroll 2] rec deref (t:t) : t =
    match view t with
    | Var {v_binding=Some u;_} -> deref u
    | _ -> t

  let vars_seq (seq:t Sequence.t) : Var.Set.t =
    let res = ref Var.Set.empty in
    let rec aux t = match view @@ deref t with
      | Var v -> res := Var.Set.add v !res
      | App {args;_} -> IArray.iter aux args
      | Eqn {lhs;rhs;_} -> aux lhs; aux rhs
    in
    seq aux;
    !res

  let vars t = vars_seq (Sequence.singleton t)

  (* follow variable bindings deeply *)
  let rec deref_deep t : t = match view t with
    | Var {v_binding=Some u;_} -> deref_deep u
    | Var _ -> t
    | App {f; args} ->
      let args' = IArray.map deref_deep args in
      if IArray.equal (==) args args' then t else app f args'
    | Eqn {sign;lhs;rhs} ->
      let lhs' = deref_deep lhs in
      let rhs' = deref_deep rhs in
      if lhs==lhs' && rhs==rhs' then t else eqn ~sign lhs' rhs'

  let rename (r:Renaming.t) (t:t) : term =
    let rec aux t = match view t with
      | Var v when Var.marked v -> t (* part of the renaming *)
      | Var {v_binding=Some u;_} -> aux u (* follow *)
      | Var v ->
        (* [v] is not bound, rename it to [v'] *)
        let v' = Var.copy v in
        Var.mark v';
        Vec.push r v'; (* do not rename [v'] *)
        let u = var v' in
        v.v_binding <- Some u;
        u
      | App {f; args} ->
        let args' = IArray.map aux args in
        if IArray.equal (==) args args' then t else app f args'
      | Eqn {sign; lhs; rhs} ->
        let lhs' = aux lhs in
        let rhs' = aux rhs in
        if lhs==lhs' && rhs==rhs' then t
        else eqn ~sign lhs' rhs'
    in aux t

  let rename_arr r = IArray.map (rename r)
end

module Rule = struct
  type t = rule

  let concl r = r.rule_concl
  let body r = r.rule_body
  let equal a b : bool =
    Term.equal (concl a) (concl b) && IArray.equal Term.equal (body a) (body b)

  let rename_in_place r : unit =
    Renaming.with_
      (fun ren ->
         r.rule_concl <- Term.rename ren r.rule_concl;
         r.rule_body <- Term.rename_arr ren r.rule_body)

  let pp out (r:t) =
    Format.fprintf out "(@[%a <- %a@])" Term.pp (concl r) (pp_iarray Term.pp) (body r)
end

module Undo_stack : sig
  type t

  val push_bind : t -> Var.t -> term -> unit
  (** [push_bind undo v t] bindings [v] to [t] and remembers to undo
      this binding in [undo] *)

  val create : unit -> t

  val clear : t -> unit

  val with_ : ?undo:t -> (t -> 'a) -> 'a
end = struct
  type t = Var.t Vec.vector

  type level = int

  let create () : t = Vec.create ()

  let[@inline] save (st:t) : level = Vec.size st

  let[@inline] push_bind (st:t) (v:var) (t:term) : unit =
    Vec.push st v;
    assert (v.v_binding = None);
    v.v_binding <- Some t;
    ()

  let restore st lvl : unit =
    while Vec.size st > lvl do
      let v = Vec.pop_exn st in
      v.v_binding <- None;
    done

  let clear st = restore st 0

  let with_ ?(undo=create()) f =
    let lvl = save undo in
    try
      let x = f undo in
      restore undo lvl;
      x
    with e ->
      restore undo lvl;
      raise e
end

module Unif = struct
  exception Fail

  type op = O_unif | O_match

  let occurs_check v t : bool =
    assert (v.v_binding = None);
    let rec aux t =
      let t = Term.deref t in
      match Term.view t with
      | Var v' -> Var.equal v v'
      | App {args; f=_} -> IArray.exists aux args
      | Eqn {lhs; rhs; sign=_} -> aux lhs || aux rhs
    in aux t

  let unif_ op undo a b : unit =
    let rec aux a b =
      let a = Term.deref a in
      let b = Term.deref b in
      match Term.view a, Term.view b with
      | Var v1, Var v2 when Var.equal v1 v2 -> ()
      | Var v, _ ->
        if occurs_check v b then raise Fail;
        Undo_stack.push_bind undo v b
      | _, Var v when (match op with O_unif -> true | O_match -> false) ->
        (* can bind var on the RHS, if we're doing full unif and not just matching *)
        if occurs_check v a then raise Fail;
        Undo_stack.push_bind undo v a
      | App r1, App r2
        when Fun.equal r1.f r2.f && IArray.length r1.args = IArray.length r2.args ->
        IArray.iter2 aux r1.args r2.args
      | Eqn r1, Eqn r2 when r1.sign = r2.sign ->
        aux r1.lhs r2.lhs;
        aux r1.rhs r2.rhs;
      | App _, _ | Eqn _, _
        -> raise Fail
    in
    aux a b

  let unify ~undo a b = unif_ O_unif undo a b
  let match_ ~undo a b = unif_ O_match undo a b
end

