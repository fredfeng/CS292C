exception NotImplemented

(** Report an error message that some functionality at level [i]
    has not been implemented. If dummy is [Some x], return [x]. 
    Otherwise, raise [NotImplemented].  *)
let at_level ?dummy (i : int) ~(msg : string) : 'a =
  Logs.err (fun m -> m "TODO at level %d: %s" i msg);
  match dummy with None -> raise NotImplemented | Some x -> x
