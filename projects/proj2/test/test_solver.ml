open Base

exception Timeout

(* run a function with specified timeout:
   https://discuss.ocaml.org/t/computation-with-time-constraint/5548/9 *)
let with_timeout timeout f =
  let _ =
    Stdlib.Sys.set_signal Stdlib.Sys.sigalrm
      (Stdlib.Sys.Signal_handle (fun _ -> raise Timeout))
  in
  ignore (Unix.alarm timeout);
  try
    let r = f () in
    ignore (Unix.alarm 0);
    r
  with e ->
    ignore (Unix.alarm 0);
    raise e

let bench_dir = "bench"
let csv_filename = "bench.csv"

type exp = Sat | Unsat [@@deriving equal]

let pp_exp = Fmt.(using (function Sat -> "sat" | Unsat -> "unsat") string)
let exp_to_dir = Fmt.to_to_string pp_exp
let ( ++ ) = Stdlib.Filename.concat

type which = Dpll | Cdcl [@@deriving equal]

let pp_which = Fmt.(using (function Dpll -> "dpll" | Cdcl -> "cdcl") string)

let init () =
  Logs.set_reporter (Logs.format_reporter ());
  Logs.set_level (Some Logs.Debug)

let path_of ~suite ~exp file = bench_dir ++ (suite ++ (exp_to_dir exp ++ file))

let test_case filename desc which ~sat ~verify_proof () =
  let solve =
    match which with Dpll -> Solver.Dpll.run | _ -> Solver.Cdcl.run
  in
  Logs.debug (fun m -> m "Solving %s" filename);
  try
    let soln = with_timeout 30 (fun () -> solve desc) in
    if sat then Solver.Solution.verify_sat desc soln
    else if verify_proof then Solver.Solution.verify_unsat desc soln;
    Alcotest.(check' bool)
      ~expected:sat
      ~actual:(Solver.Solution.is_sat soln)
      ~msg:filename
  with _ -> Alcotest.fail filename

type scenario = which * exp * bool

let pp_scenario ppf (which, exp, verify_proof) =
  if verify_proof then Fmt.pf ppf "%a-proof" pp_which which
  else Fmt.pf ppf "%a-%a" pp_which which pp_exp exp

let scenarios =
  [
    (Dpll, Sat, false);
    (Dpll, Unsat, false);
    (Cdcl, Sat, false);
    (Cdcl, Unsat, false);
    (Dpll, Unsat, true);
    (Cdcl, Unsat, true);
  ]

let suites =
  bench_dir ++ csv_filename
  |> Csv.load
  |> Csv.to_array
  |> Array.to_list
  |> List.concat_map ~f:(function
       | [| suite; which |] when String.(which = "common") ->
           [ (suite, Dpll); (suite, Cdcl) ]
       | [| suite; "cdcl" |] -> [ (suite, Cdcl) ]
       | ss ->
           Logs.err Fmt.(fun m -> m "Invalid line: %a" (array string) ss);
           failwith "test_solver")

let cases =
  suites
  |> List.map ~f:fst
  |> List.dedup_and_sort ~compare:String.compare
  |> List.concat_map ~f:(fun suite ->
         let parse_cases exp =
           let cnf_list = path_of ~suite ~exp "cnf" in
           let lines = Stdio.In_channel.read_lines cnf_list in
           List.map lines ~f:(fun cnf_file ->
               ( cnf_file,
                 Dimacs_parser.parse_file (path_of ~suite ~exp cnf_file) ))
         in
         List.concat_map [ Sat; Unsat ] ~f:(fun exp ->
             List.map (parse_cases exp) ~f:(fun r -> ((suite, exp), r))))

let test_scenario scenario =
  let which, exp, verify_proof = scenario in

  Alcotest.run
    (Fmt.str "%a" pp_scenario scenario)
    (suites
    |> List.filter ~f:(fun (_, which') -> equal_which which which')
    |> List.map ~f:(fun (suite, _) ->
           ( suite,
             List.filter cases ~f:(fun ((suite', exp'), (_, _)) ->
                 String.(suite = suite') && equal_exp exp exp')
             |> List.map ~f:(fun (_, (filename, desc)) ->
                    Alcotest.test_case filename `Quick
                      (test_case filename desc which
                         ~sat:(match exp with Sat -> true | _ -> false)
                         ~verify_proof)) )))
