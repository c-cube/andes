
open Util

module Var : sig
  type t

  val make : string -> t
  val makef : ('a, Format.formatter, unit, unit, unit, t) format6 -> 'a
  val copy : t -> t
  val fresh : unit -> t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val pp : t CCFormat.printer

  module Map : CCMap.S with type key = t
  module Set : CCSet.S with type elt = t
end

type rule

module Fun : sig
  type t

  type kind = private
    | F_cstor
    | F_defined of {
        mutable rules: rule list;
        recursive: bool;
        mutable n_rec_calls: int; (* number of recursive sub-calls *)
      }

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val pp : t CCFormat.printer
  val to_string : t -> string

  val id : t -> ID.t
  val kind : t -> kind
  val arity : t -> int

  val is_recursive : t -> bool
  val is_defined : t -> bool

  type rule_promise

  val mk_cstor : ID.t -> arity:int -> t
  val mk_defined :
    ID.t ->
    arity:int -> recursive:bool ->
    t * rule_promise
end

(** {2 Variable renaming} *)
module Renaming : sig
  type t

  val with_ : (t -> 'a) -> 'a
end

type term

(** Substitutions *)
module Subst : sig
  type t
  val empty : t
  val add : t -> Var.t -> term -> t
  val mem : t -> Var.t -> bool
  val get : t -> Var.t -> term option
  val to_iter : t -> (Var.t * term) Iter.t
  val pp : t Fmt.printer
end

module Term : sig
  type t = term

  type view =
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

  val view : t -> view

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val pp : t CCFormat.printer

  module Tbl : CCHashtbl.S with type key = t
  module Set : CCSet.S with type elt = t

  val var : Var.t -> t
  val app : Fun.t -> t array -> t
  val app_l : Fun.t -> t list -> t
  val const : Fun.t -> t
  val eq : t -> t -> t
  val neq : t -> t -> t
  val eqn : sign:bool -> t -> t -> t

  val deref_var : Subst.t -> t -> t
  (** If [t] is a variable bound in [subst], replace it, and recursively.
      Otherwise return [t]. *)

  val is_ground : t -> bool
  val subterms : ?tbl:unit Tbl.t -> ?enter:(t->bool) -> t -> t Iter.t
  val contains_var : ?tbl:unit Tbl.t -> Var.t -> t -> bool
  val vars_iter : ?tbl:unit Tbl.t -> t Iter.t -> Var.Set.t
  val vars : ?tbl:unit Tbl.t -> t -> Var.Set.t

  val is_var : t -> bool
  val as_var_exn : t -> Var.t

  val rename : ?cache:t Tbl.t -> Renaming.t -> t -> t
  val rename_arr : ?cache:t Tbl.t -> Renaming.t -> t array -> t array

  val apply_subst : ?cache:t Tbl.t -> Subst.t -> t -> t
end

(** {2 Generalized Clause} *)
module Clause : sig
  type t = private {
    concl: Term.t array; (* non empty *)
    guard: Term.t array;
  }

  val concl : t -> Term.t array
  val guard : t -> Term.t array

  val rename : ?cache:Term.t Term.Tbl.t -> t -> t

  val apply_subst : ?cache:Term.t Term.Tbl.t -> Subst.t -> t -> t

  val equal : t -> t -> bool
  val make : Term.t array -> Term.t array -> t
  val pp : t CCFormat.printer
end

module Rule : sig
  type t = rule
  (** A rule, that is, a Horn clause where the LHS (concl) is
      a term whose head is a defined function.
      Invariant: each rule has a set of variables that occur nowhere else.
      Use {!rename_in_place} to enforce this invariant whenever the rule
      is used *)

  val concl: t -> Term.t
  val body : t -> Term.t array

  val make : Term.t -> Term.t array -> t
  (** [make concl body] makes a rule.
      @raise Util.Error if the conclusion is not a defined function application *)

  val make_l : Term.t -> Term.t list -> t

  val to_clause : t -> Clause.t
  val head : t -> Fun.t

  val add_to_def : ?n_rec_calls:int -> Fun.rule_promise -> t list -> unit
  (** Define the set of rules for this function *)

  val rename_in_place : t -> unit
  (** rename variables of this rule *)

  val equal : t -> t -> bool
  val pp : t CCFormat.printer
end

(** {2 Unification of terms} *)
module Unif : sig
  exception Fail

  val can_bind : Subst.t -> Var.t -> Term.t -> bool

  val unify : Subst.t -> Term.t -> Term.t -> Subst.t
  (** [unify t1 t2] returns [()] in case of success (binding variables
      in [t1] and [t2] to make them equal).
      @raise Fail if the terms could not be unified *)

  val match_ : Subst.t -> Term.t -> Term.t -> Subst.t
  (** [match_ t1 t2] returns [()] in case of success (binding variables
      in [t1] to make them equal).
      @raise Fail if the terms could not be unified *)

end

