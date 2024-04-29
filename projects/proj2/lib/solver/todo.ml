open Base

exception NotImplemented

let part ?dummy (n : int) (msg : string) : 'a =
  match dummy with
  | None ->
      Logs.err (fun m -> m "Part %d: %s" n msg);
      raise NotImplemented
  | Some x ->
      Logs.warn (fun m -> m "Part %d: %s" n msg);
      x
