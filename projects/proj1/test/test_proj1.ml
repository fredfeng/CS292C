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

let public_dir = "public"
let public_csv_filename = "bench.csv"

let public_cases =
  Stdlib.Filename.concat public_dir public_csv_filename
  |> Csv.load
  |> Csv.to_array
  |> Array.filter_map ~f:(function
       | [| filename; category |] ->
           Option.map (Int.of_string_opt category) ~f:(fun n -> (filename, n))
       | _ -> None)
  |> Array.to_list
  |> List.sort ~compare:(fun (_, n1) (_, n2) -> Int.compare n1 n2)

type result = Verified | NotVerified | Unknown [@@deriving compare, equal]

let pp_result : result Fmt.t =
  Fmt.using
    (function
      | Verified -> "verified"
      | NotVerified -> "not verified"
      | Unknown -> "unknown")
    Fmt.string

let parse_result : string -> result option = function
  | "verified" -> Some Verified
  | "not verified" -> Some NotVerified
  | "unknown" -> Some Unknown
  | _ -> None

type out = string * result [@@deriving compare, equal]
(** (method_name, result) pair *)

let pp_out : out Fmt.t =
  let open Fmt in
  pair ~sep:(any ": ") string pp_result

let out_buffer = Buffer.create 1000
let out_buffer_formatter = Fmt.with_buffer out_buffer
let _ = Logs.set_reporter (Logs.format_reporter ~app:out_buffer_formatter ())
let _ = Logs.set_level (Some Logs.Debug)

let parse_exp_list out_list_str : out list =
  out_list_str
  |> String.split_lines
  |> List.filter_map ~f:(fun line ->
         match String.split ~on:':' line with
         | [ method_name; result_str ] -> (
             match parse_result (String.strip result_str) with
             | Some result -> Some (String.strip method_name, result)
             | None ->
                 Logs.err (fun m -> m "Invalid result: %s" result_str);
                 Logs.warn (fun m -> m "Ignoring line: %s" line);
                 None)
         | _ ->
             Logs.warn (fun m -> m "Ignoring line: %s" line);
             None)

let validate_out_list rs =
  let rec go = function
    | [] -> ()
    | (method_name, _) :: rest ->
        if List.Assoc.mem rest ~equal:String.equal method_name then (
          Logs.err (fun m -> m "Duplicate result for method: %s" method_name);
          Logs.err (fun m -> m "in %a" Fmt.(list pp_out) rs);
          failwith "validate_out_list");
        go rest
  in
  match rs with
  | [] ->
      Logs.err (fun m -> m "Empty result list");
      failwith "validate_out_list"
  | _ ->
      ();
      go rs

let t_exp_list =
  Alcotest.testable
    Fmt.(vbox @@ list pp_out)
    (fun l1 l2 ->
      List.equal equal_out
        (List.dedup_and_sort ~compare:compare_out l1)
        (List.dedup_and_sort ~compare:compare_out l2))

let test_case ~dir filename () =
  let dfy_path = Stdlib.Filename.concat dir filename in
  let prog = Lib.Parser.Prog.parse_file dfy_path in
  let expected =
    dfy_path ^ ".expected" |> Stdio.In_channel.read_all |> parse_exp_list
  in
  Logs.info (fun m -> m "Validating expected results");
  let () = validate_out_list expected in
  Logs.info (fun m -> m "Running verifier");
  Buffer.reset out_buffer;
  let () = with_timeout 10 (fun () -> List.iter prog ~f:(Lib.Verify.go prog)) in
  let actual = Buffer.contents out_buffer |> parse_exp_list in
  Logs.info (fun m -> m "Validating actual results");
  let () = validate_out_list actual in
  Logs.info (fun m -> m "Comparing actual results with expected results");
  Alcotest.(check' t_exp_list) ~expected ~actual ~msg:filename

let () =
  Alcotest.run "difny"
    [
      ( "public",
        List.map public_cases ~f:(fun (filename, n) ->
            Alcotest.test_case
              Fmt.(str "[cat: %d] %s" n filename)
              `Quick
              (test_case ~dir:"public" filename)) );
    ]
