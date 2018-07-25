
(** {1 Logic Programming Tool} *)

(** Unique Identifiers *)
module ID = ID

module Term = Types.Term
module Var = Types.Var

module Log : sig
  val enable : int -> unit
end

module Solution : sig
  type t = {
    subst: Term.t Var.Map.t;
    constr: Term.t list; (* constraints *)
  }

  val pp : t CCFormat.printer
end

type goal = Term.t list

module Config : sig
  type t = {
    max_step: int;
  }

  val default : t
  val pp : t CCFormat.printer
end

val solve : ?config:Config.t -> goal -> Solution.t option
(** [solve goal] returns the first solution to the given goal *)
