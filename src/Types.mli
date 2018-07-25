
module Var : sig
  type t

  val make : string -> t
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
      }

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val pp : t CCFormat.printer

  val kind : t -> kind
  val mk_cstor : ID.t -> arity:int -> t
  val mk_defined : ID.t -> arity:int -> t
end

(** {2 Variable renaming} *)
module Renaming : sig
  type t

  val with_ : (t -> 'a) -> 'a
end

module Term : sig
  type t

  type view =
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

  val view : t -> view

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val pp : t CCFormat.printer

  val var : Var.t -> t
  val app : Fun.t -> t IArray.t -> t
  val app_l : Fun.t -> t list -> t
  val const : Fun.t -> t
  val eq : t -> t -> t
  val neq : t -> t -> t
  val eqn : sign:bool -> t -> t -> t

  val vars_seq : t Sequence.t -> Var.Set.t
  val vars : t -> Var.Set.t

  val is_var : t -> bool

  val deref_deep : t -> t
  (** [deref_deep t] rebuilds a new term where variables are replaced by their
      current binding *)

  val rename : Renaming.t -> t -> t
  val rename_arr : Renaming.t -> t IArray.t -> t IArray.t
end

module Rule : sig
  type t = rule
  (** A rule, that is, a Horn clause where the LHS (concl) is
      a term whose head is a defined function.
      Invariant: each rule has a set of variables that occur nowhere else.
      Use {!rename_in_place} to enforce this invariant whenever the rule
      is used *)

  val concl: t -> Term.t
  val body : t -> Term.t IArray.t

  val rename_in_place : t -> unit
  (** rename variables of this rule *)

  val equal : t -> t -> bool
  val pp : t CCFormat.printer
end

(** {2 Stack to undo changes to terms} *)
module Undo_stack : sig
  type t

  val create : unit -> t
  (** Make a new stack *)

  val clear : t -> unit
  (** clear for re-using *)

  val with_ : ?undo:t -> (t -> 'a) -> 'a
  (** [with_ f] saves the current state of the undo stack,
      calls [f undo], then restores variables to the old saved state.
      @param undo if provided, start from this undo stack *)
end


(** {2 Unification of terms} *)
module Unif : sig
  exception Fail

  val unify : undo:Undo_stack.t -> Term.t -> Term.t -> unit
  (** [unify t1 t2] returns [()] in case of success (binding variables
      in [t1] and [t2] to make them equal).
      @raise Fail if the terms could not be unified *)

  val match_ : undo:Undo_stack.t -> Term.t -> Term.t -> unit
  (** [match_ t1 t2] returns [()] in case of success (binding variables
      in [t1] to make them equal).
      @raise Fail if the terms could not be unified *)

end

