open Base
open Cmdliner

type action = CRun | CVerify
type verb = Debug | Info | Quiet
type conf = { action : action; file_opt : string option; verb : verb }

(** Perform action *)
let go { action; file_opt; verb } =
  Logs.set_reporter (Logs_fmt.reporter ());
  Lib.Parser.Prog.pp_exceptions ();
  (match verb with
  | Quiet -> Logs.set_level (Some Logs.Error)
  | Debug -> Logs.set_level (Some Logs.Debug)
  | Info -> Logs.set_level (Some Logs.Info));
  let open Lib in
  let p =
    match file_opt with
    | Some file ->
        Logs.info (fun m -> m "<<< Parsing file %s" file);
        Parser.Prog.parse_file file
    | None ->
        (* read from stdin *)
        Logs.info (fun m -> m "<<< Reading from stdin");
        Parser.Prog.parse_chan Stdio.stdin
  in
  Logs.info (fun m -> m ">>> Parsed:");
  Logs.info (fun m -> m "%a" Pretty.prog p);

  match action with
  | CRun ->
      p
      |> List.find ~f:(fun meth -> String.(meth.Lang.id = "Main"))
      |> Option.value_exn ~error:(Error.of_string "Main method not found")
      |> Eval.eval_meth p
  | CVerify -> List.iter p ~f:(Verify.go p)

let file_term =
  Arg.(
    value
    & pos 0 (some Arg.file) None
    & info [] ~docv:"FILE" ~doc:"input difny file")

let verb_term =
  let level = Arg.enum [ ("debug", Debug); ("info", Info); ("quiet", Quiet) ] in
  Arg.(
    value & opt level Quiet
    & info [ "v" ] ~docv:"VERBOSITY" ~doc:"verbosity level (quiet|info|debug)")

let term_of_action action k =
  let combine file_opt verb = { action; file_opt; verb } |> k in
  Term.(const combine $ file_term $ verb_term)

let cmd_verify k =
  let doc = "verify the program" in
  let info = Cmd.info "verify" ~doc in
  Cmd.v info (term_of_action CVerify k)

let cmd_run k =
  let doc = "execute the program" in
  let info = Cmd.info "run" ~doc in
  Cmd.v info (term_of_action CRun k)

let root_info =
  Cmd.info "difny" ~doc:"difny is a verification-aware programming language"

let parse_command_line_and_run k =
  Cmd.group root_info [ cmd_verify k; cmd_run k ] |> Cmd.eval |> Stdlib.exit

let main () = parse_command_line_and_run go
let () = main ()
