
(** {1 Compile TIP problem into a Logic problem} *)

open Andes

module Term = Andes.Term
module A = Ast

type builtins = {
  true_: Fun.t;
  false_: Fun.t;
  and_: Fun.t;
  or_: Fun.t;
  imply: Fun.t;
  eq: Fun.t;
  not_: Fun.t;
}

type t = {
  funs : Fun.t ID.Tbl.t;
  builtins: builtins;
  mutable goal : Term.t list;
  mutable n: int;
}

let mk_builtins () : builtins =
  let true_ = Fun.mk_cstor (ID.make "true") ~arity:0 in
  let false_ = Fun.mk_cstor (ID.make "false") ~arity:0 in
  let and_, def_and = Fun.mk_defined (ID.make "and") ~arity:3 in
  let or_, def_or = Fun.mk_defined (ID.make "or") ~arity:3 in
  let imply, def_imply = Fun.mk_defined (ID.make "=>") ~arity:3 in
  let eq, def_eq = Fun.mk_defined (ID.make "=") ~arity:3 in
  let not_, def_not = Fun.mk_defined (ID.make "not") ~arity:2 in
  let module T = Term in
  let x = T.var @@ Var.make "x" in
  let y = T.var @@ Var.make "y" in
  (* [and true true true]
     [and false y false]
     [and x false false] *)
  let true_t = T.const true_ in
  let false_t = T.const false_ in
  Rule.add_to_def def_and
    [ Rule.make_l (T.app_l and_ [true_t; true_t; true_t]) [];
      Rule.make_l (T.app_l and_ [false_t; y; false_t]) [];
      Rule.make_l (T.app_l and_ [x; false_t; false_t]) [];
    ];
  (* [or false false false]
     [or true y true]
     [or x true true] *)
  Rule.add_to_def def_or
    [ Rule.make_l (T.app_l or_ [false_t; false_t; false_t]) [];
      Rule.make_l (T.app_l or_ [true_t; y; true_t]) [];
      Rule.make_l (T.app_l or_ [x; true_t; true_t]) [];
    ];
  (* [imply false _ true]
     [imply true x x] *)
  Rule.add_to_def def_imply
    [ Rule.make_l (T.app_l imply [false_t; x; true_t]) [];
      Rule.make_l (T.app_l imply [true_t; x; x]) [];
    ];
  (* [eq x x true]
     [eq x y false <- x!=y] *)
  Rule.add_to_def def_eq
    [ Rule.make_l (T.app_l eq [x; x; true_t]) [];
      Rule.make_l (T.app_l eq [x; y; false_t]) [T.neq x y];
    ];
  (* [not false true]
     [not true false] *)
  Rule.add_to_def def_not
    [ Rule.make_l (T.app_l not_ [false_t; true_t]) [];
      Rule.make_l (T.app_l not_ [true_t; false_t]) [];
    ];
  let b = {
    true_; false_; and_; or_; not_; eq; imply;
  } in
  b

let create() : t =
  let st = {
    funs=ID.Tbl.create 16;
    builtins=mk_builtins ();
    goal=[];
    n=0;
  } in
  st

let[@inline] goal st : Term.t list = st.goal

let unimplemented s = Util.errorf "not implemented: compile %s" s

(* generator of fresh IDs *)
module Gensym : sig
  type t
  val create : unit -> t
  val fresh_var : t -> Var.t
end = struct
  type t = int ref
  let create () = ref 0
  let fresh_s =
    let vars = "xyzuvw" in
    fun n ->
      let x = CCRef.get_then_incr n in
      let d, q = x mod (String.length vars), x / String.length vars in
      Printf.sprintf "%c%s" vars.[d] (if q=0 then "" else string_of_int q)
  let fresh_var r = Var.make (fresh_s r)
end

(** {2 Functional Substitutions}
    Mostly useful for preprocessing *)
module Subst : sig
  type t = Term.t Var.Map.t

  val empty : t
  val mem : Var.t -> t -> bool
  val add : Var.t -> Term.t -> t -> t

  val apply : t -> Term.t -> Term.t
end = struct
  module M = Var.Map
  type t = Term.t Var.Map.t
  let mem = M.mem
  let empty = M.empty
  let add v t m = M.add v t m

  let apply s (t:Term.t) : Term.t =
    Types.Undo_stack.with_
      (fun undo ->
         M.iter (fun v t -> Types.Undo_stack.push_bind undo v t) s;
         Term.deref_deep t)
end

module M_state = struct
  type t = {
    subst: Subst.t;
    guards: Term.t list;
  }
  let empty = {subst=Subst.empty; guards=[]}
  let add_guard t m = {m with guards=t::m.guards}
  let add_subst v t m = {m with subst = Subst.add v t m.subst}

  let add_eq t u m =
    match Term.view t with
    | Term.Var x when not @@ Subst.mem x m.subst -> add_subst x u m
    | _ -> add_guard (Term.eq t u) m
end

module M = Monad_choice.Make(M_state)

(* compile [f vars = body] into a set of rules for [f]
   @param res_eq if provided, add constraints that [body = res_eq]
*)
let compile_fun ?res_eq (st:t) (f:Fun.t) (vars:A.var list) (body:A.term) : Rule.t list =
  let open M.Infix in
  let g = Gensym.create() in
  (* map [A.var] to [Var.t] *)
  let get_a_var =
    let var_tbl : Var.t ID.Tbl.t = ID.Tbl.create 6 in
    fun v ->
      ID.Tbl.get_or_add var_tbl ~k:(A.Var.id v) ~f:(fun id -> Var.make @@ ID.name id)
  in
  let t_vars = List.map get_a_var vars in
  (* transform [t] into a constructor [Term.t], pushing all defined functions
     into the rule's guard, using fresh variables to name intermediate
     values *)
  let rec aux subst (t:A.term) : Term.t M.t =
    match t.A.term with
    | A.If (a,b,c) ->
      (* [if a b c] becomes [b <- a=true] and [c <- a=false] *)
      aux subst a >>= fun a ->
      M.append
        (M.update (M_state.add_eq a @@ Term.const st.builtins.true_)
         >>= fun () -> aux subst b)
        (M.update (M_state.add_eq a @@ Term.const st.builtins.false_)
         >>= fun () -> aux subst c)
    | A.Bool true -> M.return @@ Term.const st.builtins.true_
    | A.Bool false -> M.return @@ Term.const st.builtins.false_
    | A.Var v when A.Var_map.mem v subst -> M.return @@ A.Var_map.find v subst
    | A.Var v -> M.return @@ Term.var @@ get_a_var v
    | A.Const c ->
      aux_app subst c []
    | A.App (f, args) ->
      begin match f.A.term with
        | A.Const f ->
          aux_app subst f args
        | _ -> unimplemented "HO application"
      end
    | A.Match (t, cases) ->
      (* [match t (c_i vars -> rhs_i)] becomes a bunch of [rhs_i <- t = c_i vars] *)
      aux subst t >>= fun t ->
      ID.Map.to_list cases
      |> List.rev_map
        (fun (c,(vars,rhs)) ->
           let c =
             try ID.Tbl.find st.funs c
             with Not_found -> Util.errorf "cannot find constructor %a" ID.pp c
           in
           let vars = List.map get_a_var vars in
           (* push guard [t = c(vars)], return [rhs] *)
           let c_term = Term.app_l c (List.map Term.var vars) in
           M.update (M_state.add_eq t c_term) >>= fun () ->
           aux subst rhs)
      |> M.append_l
    | A.Not {A.term=A.Not t;_} -> aux subst t (* [not (not t) --> t] *)
    | A.Not u ->
      (* add [not u res], return [res] *)
      aux subst u >>= fun u ->
      let res = Term.var @@ Gensym.fresh_var g in
      M.update (M_state.add_guard @@ Term.app_l st.builtins.not_ [u; res]) >|= fun () ->
      res
    | A.Binop (op, a, b) ->
      (* [not u x], return x *)
      aux subst a >>= fun a ->
      aux subst b >>= fun b ->
      let res = Term.var @@ Gensym.fresh_var g in
      let f = match op with
        | A.And -> st.builtins.and_
        | A.Or -> st.builtins.or_
        | A.Imply -> st.builtins.imply
        | A.Eq -> st.builtins.eq
      in
      M.update (M_state.add_guard @@ Term.app_l f [a; b; res]) >|= fun () ->
      res
    | A.Let (v,t,u) ->
      (* expand on the fly *)
      aux subst t >>= fun t ->
      let subst = A.Var_map.add v t subst in
      aux subst u
    | A.Unknown _ -> unimplemented "unknown"
    | A.Asserting _ -> unimplemented "asserting"
    | A.Undefined_value -> unimplemented "undefined"
    | A.Switch _
    | A.Bind _
    | A.Select _
      -> unimplemented (Format.asprintf "%a" A.pp_term t)
  and aux_app subst f args =
    let f =
      try ID.Tbl.find st.funs f
      with Not_found -> Util.errorf "unknown function %a" ID.pp f
    in
    begin match Fun.kind f with
      | Fun.F_cstor ->
        M.map_l (aux subst) args >|= Term.app_l f
      | Fun.F_defined _ ->
        (* introduce a variable [res] for the result of [f args],
           push [f args…res] into guard, return [res] *)
        let res = Term.var @@ Gensym.fresh_var g in
        M.map_l (aux subst) args >>= fun args ->
        M.update (M_state.add_guard (Term.app_l f (args @ [res]))) >|= fun () ->
        res
    end
  in
  begin
    aux A.Var_map.empty body
    |> M.run_list
    |> CCList.filter_map
      (fun (res,{M_state.subst;guards}) ->
         (* produce a rule *)
         let args = List.map (Subst.apply subst) @@ (List.map Term.var t_vars @ [res]) in
         let concl = Term.app_l f args in
         let guards = List.map (Subst.apply subst) guards in
         let constr_res_eq = match res_eq with
           | None -> None
           | Some t -> Some (Term.eq t res)
         in
         let guards = CCList.cons_maybe constr_res_eq guards in
         let r = Rule.make_l concl guards in
         Log.logf 5
           (fun k->k "(@[compile-fun.yield_rule@ :fun %a@ :rule %a@])" Fun.pp f Rule.pp r);
         (* simplify rule *)
         Simplify.simplify_rule r)
  end

(* compile recursive functions into relational functions *)
let compile_defs (st:t) (defs:A.definition list) : unit =
  let funs =
    List.map
      (fun (f,ty,body) ->
         let args, _ret = A.Ty.unfold ty in
         let arity = 1 + List.length args in (* need an additional arg for return value *)
         let fun_, rule_add = Fun.mk_defined f ~arity in
         ID.Tbl.add st.funs f fun_;
         let vars, body = A.unfold_fun body in
         assert (List.length vars + 1 = arity);
         fun_, vars, body, rule_add)
      defs
  in
  (* now compile rules *)
  List.iter
    (fun (f, vars, body, rule_add) ->
       let rules = compile_fun st f vars body in
       Rule.add_to_def rule_add rules)
    funs

(* compile a term into a relational form, possibly introducing an auxiliary
   function to encode its control flow
   @param vars parameters to the term (and its auxiliary function)
*)
let compile_term ?(name="term") ?eq ?(vars=[]) (st:t) (t:A.term) : Term.t list =
  let f, add_rules =
    Fun.mk_defined (ID.makef "aux_%s_%d" name st.n) ~arity:(List.length vars + 1) in
  let u =
    match compile_fun ?res_eq:eq st f vars t with
    | [] -> []
(*     | [r] -> Rule.body r |> IArray.to_list *)
    | rules ->
      (* define the function, and return [f vars] as goal *)
      ID.Tbl.add st.funs (Fun.id f) f;
      Rule.add_to_def add_rules rules;
      let vars = List.map (fun v -> Term.var @@ Var.make @@ ID.name @@ A.Var.id v) vars in
      (* also add a result parameter *)
      let res = match eq with
        | Some t -> t
        | None -> Term.var @@ Var.make "result"
      in
      [Term.app_l f (vars @ [res])]
  in
  Log.logf 5
    (fun k->k "(@[compile-term@ %a@ :into [@[<hv>%a@]]@])" A.pp_term t (Util.pp_list Term.pp) u);
  u

let add_cstor st id ~arity =
  let fun_ = Fun.mk_cstor id ~arity in
  ID.Tbl.add st.funs id fun_

(* process one statement *)
let add_stmt (st:t) (stmt:A.statement) : unit =
  Log.logf 2 (fun k->k "(@[compile.add_stmt@ %a@])" A.pp_statement stmt);
  match stmt with
  | A.Data tys ->
    (* define the constructors *)
    List.iter
      (fun {A.Ty.data_cstors;_} ->
         ID.Map.iter
           (fun c ty_c ->
              let args, _ = A.Ty.unfold ty_c in
              let arity = List.length args in
              add_cstor st c ~arity)
           data_cstors)
      tys
  | A.TyDecl _ -> ()
  | A.Decl (_, _) -> unimplemented "uninterpreted function"
  | A.Define defs ->
    compile_defs st defs
  | A.Assert g ->
    let t = compile_term ~name:"assert" ~eq:(Term.const st.builtins.true_) st g in
    st.goal <- List.rev_append t st.goal
  | A.Goal (vars, g) ->
    let t = compile_term ~name:"goal" ~eq:(Term.const st.builtins.true_) ~vars st g in
    st.goal <- List.rev_append t st.goal

let stmts (l:A.statement list) : t =
  let st = create () in
  List.iter (add_stmt st) l;
  st
