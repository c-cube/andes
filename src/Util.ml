
module Fmt = CCFormat

let pp_iarray pp_x out a =
  CCFormat.(seq ~sep:(return "@ ") @@ pp_x) out (IArray.to_seq a)

module Log : sig
  val enable : int -> unit

  val logf : int -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit
  val log : int -> string -> unit
end = struct
  let lvl_ = ref 0

  let enable l =
    lvl_ := l;
    if l > 0 then Fmt.set_color_default true;
    ()

  let logf lvl k =
    if lvl <= !lvl_ then (
      k (fun fmt ->
        let out = Format.std_formatter in
        Format.fprintf out "@[<2>@{<Blue>[andes %d|%.3f]@}" lvl (Sys.time());
        Format.kfprintf
          (fun out -> Format.fprintf out "@]@.")
          out fmt)
    )

  let[@inline] log lvl s = logf lvl (fun k->k "%s" s)
end
