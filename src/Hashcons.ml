module type ARG = sig
  type t

  val equal : t -> t -> bool

  val hash : t -> int

  val set_id : t -> int -> unit
end

module Make (A : ARG) : sig
  type t

  val create : unit -> t

  val hashcons : t -> A.t -> A.t
end = struct
  module W = Weak.Make (A)

  type t = {
    tbl: W.t;
    mutable n: int;
  }

  let create () : t = { tbl = W.create 1024; n = 0 }

  (* hashcons terms *)
  let hashcons (self : t) t =
    let t' = W.merge self.tbl t in
    if t == t' then (
      let id = self.n in
      self.n <- 1 + id;
      A.set_id t' id
    );
    t'
end
