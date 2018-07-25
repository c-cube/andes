
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

module[@inline] Make(St : STATE) = struct
  module State = St

  type +'a t = State.t -> ('a * State.t) Seq.t

  let empty _ = Seq.empty

  let return x p = Seq.return (x,p)

  let map f m p = Seq.map (fun (x,p') -> f x,p') (m p)

  let flat_map f m p = Seq.flat_map (fun (x,p') -> f x p') (m p)

  let rec seq_append a b () =
    match a () with
    | Seq.Nil -> b ()
    | Seq.Cons (x,tl) -> Seq.Cons (x, seq_append tl b)

  let append m1 m2 p = seq_append (m1 p) (m2 p)

  let rec append_l = function
    | [] -> empty
    | [x] -> x
    | x :: tl -> append x @@ append_l tl

  let app m1 m2 p =
    Seq.flat_map
      (fun (f1,p1) -> Seq.map (fun (x2,p2) -> f1 x2, p2) (m2 p1))
      (m1 p)

  let app_right m1 m2 p = Seq.flat_map (fun (_,p1) -> m2 p1) (m1 p)

  let update f p = Seq.return ((), f p)

  let get_state p = Seq.return (p, p)

  let guard f p = if f p then Seq.return ((),p) else Seq.empty

  module Infix = struct
    let (>|=) m f = map f m
    let (>>=) m f = flat_map f m
    let (<*>) = app
    let (>>) = app_right
    let (<+>) = append
  end

  include Infix

  let rec map_l f l = match l with
    | [] -> return []
    | x :: tl -> (f x >>= fun x' -> map_l f tl >|= fun tl' ->  x'::tl')

  let run m = m State.empty
  let run_list m = run m |> Seq.fold_left (fun acc x -> x::acc) []
end
