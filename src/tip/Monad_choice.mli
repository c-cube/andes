
module Term = Andes.Term

module type STATE = sig
  type t
  val empty : t
end

module type S = sig
  module State : STATE

  type +'a t

  val empty : 'a t

  val return : 'a -> 'a t

  val update : (State.t -> State.t) -> unit t

  val map_l : ('a -> 'b t) -> 'a list -> 'b list t

  val append : 'a t -> 'a t -> 'a t

  val append_l : 'a t list -> 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t

  val flat_map : ('a -> 'b t) -> 'a t -> 'b t

  val app : ('a -> 'b) t -> 'a t -> 'b t

  (** Kill items whose state doesn't satisfy predicate *)
  val guard : (State.t -> bool) -> unit t

  (** reflect state *)
  val get_state : State.t t

  module Infix : sig
    val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
    val (>|=) : 'a t -> ('a -> 'b) -> 'b t
    val (<*>) : ('a -> 'b) t -> 'a t -> 'b t
    val (>>) : _ t -> 'b t -> 'b t
    val (<+>) : 'a t -> 'a t -> 'a t
  end
  include module type of Infix

  val run : 'a t -> ('a * State.t) Seq.t
  val run_list : 'a t -> ('a * State.t) list
end

module Make(St : STATE) : S with module State = St
