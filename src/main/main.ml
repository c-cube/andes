
open Andes

module C = Andes_tip.Compile

let solve stmts : unit =
  let goal = C.stmts stmts |> C.goal in
  match Andes.solve goal with
  | None -> Format.printf "@{<Yellow>[@<1>×]@} no solution found.@."
  | Some sol ->
    Format.printf "@{<Green>[@<1>✔]@} solution found!@ %a@." Andes.Solution.pp sol

let process_file (file:string) =
  Log.logf 1 (fun k->k "(@[@{<yellow>process-file@} %S@])" file);
  match Andes_tip.parse_file file with
  | Error msg ->
    Format.printf "@{<Red>Error@} when parsing %S:@ %s@." file msg;
    exit 1
  | Ok stmts ->
    solve stmts

let main () =
  Fmt.set_color_default true;
  let files = CCVector.create () in
  let options = [
    "-d", Arg.Int Log.enable, " enable debug";
  ] |> Arg.align in
  Arg.parse options (CCVector.push files) "andes [options] <file>";
  CCVector.iter process_file files

let () = main ()
