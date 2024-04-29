open Cmdliner

type verbose = Debug | Info | Quiet
type solver = Dpll | Cdcl

let check_proof =
  let doc = "Check the refutation proof if the solution is unsatisfiable" in
  Arg.(value & flag & info [ "c"; "check" ] ~docv:"CHECK" ~doc)

let file =
  Arg.(
    required
    & pos 0 (some Arg.file) None
    & info [] ~docv:"FILE" ~doc:"input difny file")

let verbose =
  let choices =
    Arg.enum [ ("debug", Debug); ("info", Info); ("quiet", Quiet) ]
  in
  Arg.(
    value
    & opt choices Quiet
    & info [ "v"; "verbose" ] ~docv:"VERBOSITY"
        ~doc:"verbosity level (quiet|info|debug)")

let solver =
  let choices = Arg.enum [ ("dpll", Dpll); ("cdcl", Cdcl) ] in
  Arg.(
    value
    & opt choices Cdcl
    & info [ "s"; "solver" ] ~docv:"SOLVER" ~doc:"solver to use (dpll|cdcl)")

let run verbose check_proof solver file =
  (match verbose with
  | Quiet -> Logs.set_level (Some Logs.Error)
  | Info -> Logs.set_level (Some Logs.Info)
  | Debug -> Logs.set_level (Some Logs.Debug));
  Logs.app (fun m -> m "check_proof %B" check_proof);
  Logs.set_reporter (Logs.format_reporter ());
  let desc = Dimacs_parser.parse_file file in
  let solve =
    match solver with Dpll -> Solver.Dpll.run | Cdcl -> Solver.Cdcl.run
  in
  let soln = solve desc in
  Logs.app (fun m -> m "%a" Solver.Solution.pp soln);
  Solver.Solution.verify_sat desc soln;
  if check_proof then Solver.Solution.verify_unsat desc soln

let cmd =
  let doc = "The Z4 SAT Solver" in
  let info = Cmd.info "z4" ~doc in
  Cmd.v info Term.(const run $ verbose $ check_proof $ solver $ file)

let main () = Stdlib.exit (Cmd.eval cmd)
let () = main ()
