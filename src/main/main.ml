
open Andes

module C = Andes_tip.Compile

let solve stmts : unit =
  let goal = C.stmts stmts |> C.goal in
  let config = Andes.Config.default in
  let res, steps = Andes.solve ~config goal in
  match res with
  | None -> Format.printf "@{<Yellow>[@<1>×]@} no solution found (%d steps).@." steps
  | Some sol ->
    Format.printf "@{<Green>[@<1>✔]@} solution found (%d steps)!@ %a@." steps Andes.Solution.pp sol

let process_file (file:string) =
  Log.logf 1 (fun k->k "(@[@{<yellow>process-file@} %S@])" file);
  match Andes_tip.parse_file file with
  | Error msg ->
    Format.printf "@{<Red>Error@} when parsing %S:@ %s@." file msg;
    exit 1
  | Ok stmts ->
    solve stmts

let set_timeout_ t =
  Log.logf 1(fun k->k "timeout: %ds" t);
  ignore (Unix.alarm t : int)

let main () =
  Sys.catch_break true;
  Catapult_file.with_setup @@ fun () ->

  Fmt.set_color_default true;
  let files = CCVector.create () in
  let options = [
    "-p", Arg.Unit (fun () -> Util.Status.enable true), " enable progress bar";
    "-d", Arg.Int Log.enable, " enable debug";
    "-bt", Arg.Unit (fun () -> Printexc.record_backtrace true), " enable backtraces";
    "-t", Arg.Int set_timeout_, " timeout in seconds";
    "--timeout", Arg.Int set_timeout_, " timeout in seconds";
  ] |> Arg.align in
  Arg.parse options (CCVector.push files) "andes [options] <file>";
  CCVector.iter process_file files

let () = main ()
