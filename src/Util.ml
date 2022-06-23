
module Fmt = CCFormat
module Vec = CCVector
module Tracing = Catapult.Tracing
module Option = CCOpt

let (let@) f x = f x

let pp_array pp_x out a =
  Fmt.(array ~sep:(return "@ ") @@ pp_x) out a

let pp_list pp_x out l =
  Fmt.(list ~sep:(return "@ ") pp_x) out l

let pp_iter pp_x out l =
  Fmt.(iter ~sep:(return "@ ") pp_x) out l

let[@inline] array_is_empty a = Array.length a = 0

let time_elapsed =
  let t = Unix.gettimeofday() in
  fun () -> Unix.gettimeofday() -. t

exception Error of string

let () =
  Printexc.register_printer
    (function
      | Error msg -> Some (Fmt.sprintf "@{<Red>Error@}: %s" msg)
      | _ -> None)

let errorf fmt =
  Fmt.ksprintf ~f:(fun s -> raise (Error s)) fmt

module Log : sig
  val enable : int -> unit

  val level : unit -> int
  val logf : int -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit
  val log : int -> string -> unit
end = struct
  let lvl_ = ref 0

  let enable l = lvl_ := l
  let[@inline] level () = !lvl_

  let logf_real lvl k =
    k (fun fmt ->
      let out = Format.std_formatter in
      Format.fprintf out "@[<2>@{<Blue>[andes %d|%.3f]@}@ " lvl (Sys.time());
      Format.kfprintf
        (fun out -> Format.fprintf out "@]@.")
        out fmt)

  let[@inline] logf lvl k = if lvl <= !lvl_ then logf_real lvl k
  let[@inline] log lvl s = logf lvl (fun k->k "%s" s)
end

module Status : sig
  val printf : ('a, out_channel, unit, unit) format4 -> 'a
  val print : string -> unit
  val flush : unit -> unit
  val enable : bool -> unit
end = struct
  let enabled_ = ref false
  let enable b = enabled_ := b

  (* TODO: find the proper code for "kill line" *)
  let flush_ (): unit = Printf.printf "\r%-80d\r%!" 0
  let flush (): unit = if !enabled_ && Log.level()=0 then flush_ ()

  let printf fmt =
    if !enabled_ then (
      if Log.level()=0 then flush_();
      Printf.printf "[%.2f] " (Sys.time());
      Printf.kfprintf
        (fun out -> if Log.level()>0 then output_char out '\n'; Stdlib.flush out) stdout fmt
    ) else Printf.ikfprintf (fun _ -> ()) stdout fmt
  let print s = printf "%s" s
end
