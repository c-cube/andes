
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
      if c<>0 then c else CCArray.compare compare a.args b.args
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
      CCHash.combine3 20 (Fun.hash f) (CCHash.iter hash @@ CCArray.to_iter args)
    | Eqn { sign; lhs; rhs } ->
      CCHash.combine4 30 (CCHash.bool sign) (hash lhs) (hash rhs)

  let rec pp out a : unit =
    match view a with
    | Var v -> Var.pp out v
    | App {f; args=[||]} -> Fun.pp out f
    | App {f; args} ->
      Format.fprintf out "(@[%a@ %a@])" Fun.pp f (pp_array pp) args
    | Eqn {sign;lhs;rhs} ->
      Format.fprintf out "(@[<hv>%s@ %a@ %a@])"
        (if sign then "=" else "!=") pp lhs pp rhs

  (* term builder *)
  let mk_ : view -> t =
    fun[@inline] t_view -> t_view

  let var v : t = mk_ @@ Var v

  let app f args : t =
    if Fun.arity f <> Array.length args then (
      Util.errorf "cannot apply %a (arity %d)@ to [@[%a@]]"
        Fun.pp f (Fun.arity f) (Util.pp_array pp) args
    );
    mk_ @@ App {f;args}

  let app_l f args : t = app f (Array.of_list args)
  let const f : t = app f [||]
  let eqn ~sign lhs rhs = mk_ @@ Eqn {lhs; rhs; sign}
  let eq a b : t = eqn ~sign:true a b
  let neq a b : t = eqn ~sign:false a b

  let is_var t = match view t with Var _ -> true | _ -> false

  let[@unroll 2] rec deref (t:t) : t =
    match view t with
    | Var {v_binding=Some u;_} -> deref u
    | _ -> t

  let subterms t yield : unit =
    let rec aux t =
      let t = deref t in
      yield t;
      match view t with
      | Var _ -> ()
      | App {args;_} -> Array.iter aux args
      | Eqn {lhs;rhs;_} -> aux lhs; aux rhs
    in
    aux t

  let vars_of_seq_ seq =
    seq
    |> Iter.filter_map
      (fun t -> match view t with
         | Var v -> Some v
         | _ -> None)
    |> Var.Set.of_iter

  let vars_iter (it:t Iter.t) : Var.Set.t =
    it
    |> Iter.flat_map subterms
    |> vars_of_seq_

  let vars t = vars_of_seq_ @@ subterms t

  (* follow variable bindings deeply *)
  let rec deref_deep t : t = match view t with
    | Var {v_binding=Some u;_} -> deref_deep u
    | Var _ -> t
    | App {f; args} ->
      let args' = Array.map deref_deep args in
      if CCArray.equal (==) args args' then t else app f args'
    | Eqn {sign;lhs;rhs} ->
      let lhs' = deref_deep lhs in
      let rhs' = deref_deep rhs in
      if lhs==lhs' && rhs==rhs' then t else eqn ~sign lhs' rhs'

  let rename (ren:Renaming.t) (t:t) : term =
    let rec aux t = match view t with
      | Var ({v_binding=Some u; _} as v) when Var.marked v -> u (* follow renaming *)
      | Var v ->
        (* [v] is not bound, rename it to [v'] *)
        let v' = Var.copy v in
        Var.mark v;
        Vec.push ren (v, v.v_binding);
        let u = var v' in
        v.v_binding <- Some u;
        u
      | App {f; args} ->
        let args' = Array.map aux args in
        if CCArray.equal (==) args args' then t else app f args'
      | Eqn {sign; lhs; rhs} ->
        let lhs' = aux lhs in
        let rhs' = aux rhs in
        if lhs==lhs' && rhs==rhs' then t
        else eqn ~sign lhs' rhs'
    in aux t

  let rename_arr r = Array.map (rename r)
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

  let rename c =
    Renaming.with_ (fun ren -> map (Term.rename ren) c)

  let deref_deep c = map Term.deref_deep c

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
    Renaming.with_
      (fun ren ->
         r.rule_concl <- Term.rename ren r.rule_concl;
         r.rule_body <- Term.rename_arr ren r.rule_body)

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

  let[@inline] with_ ?(undo=create()) f =
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
      | App {args; f=_} -> Array.exists aux args
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
        when Fun.equal r1.f r2.f && Array.length r1.args = Array.length r2.args ->
        Array.iter2 aux r1.args r2.args
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

