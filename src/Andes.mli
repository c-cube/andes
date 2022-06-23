
(** {1 Logic Programming Tool} *)

(** Unique Identifiers *)
module ID = ID
module Term = Types.Term
module Var = Types.Var
module Fun = Types.Fun
module Rule = Types.Rule
module Types = Types
module Simplify = Simplify

module Log : sig
  val enable : int -> unit
  val logf : int -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit
  val log : int -> string -> unit
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
  val set_max_steps : int -> t -> t
  val pp : t CCFormat.printer
end

val solve : ?config:Config.t -> goal -> Solution.t option * int
(** [solve goal] returns the first solution to the given goal, as well
    as the number of steps *)

(**/**)
module Fmt = CCFormat
module Util = Util
(**/**)
