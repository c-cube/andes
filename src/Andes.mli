
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
  val pp : t CCFormat.printer
end

val solve : ?config:Config.t -> goal -> Solution.t option
(** [solve goal] returns the first solution to the given goal *)

(**/**)
module Fmt = CCFormat
module Util = Util
module IArray = IArray
(**/**)
