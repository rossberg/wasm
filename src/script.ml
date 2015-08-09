(*
 * (c) 2015 Andreas Rossberg
 *)

open Source

(* Script representation *)

type command = command' phrase
and command' =
  | Memory of int
  | Define of Syntax.modul
  | Invoke of int * Syntax.expr list

type script = command list


(* Execution *)

let current_memory : Memory.t option ref = ref None
let current_module : Eval.modul option ref = ref None

let trace name = if !Flags.trace then print_endline ("-- " ^ name)

let run_command cmd =
  try
    match cmd.it with
    | Memory n ->
      trace "Allocating...";
      current_memory := Some (Memory.create n)
    | Define m ->
      trace "Checking...";
      Check.check_module m;
      if !Flags.print_sig then begin
        trace "Signature:";
        Print.print_module_sig m
      end;
      let mem = match !current_memory with
        | Some mem -> mem
        | None -> Error.error cmd.at "no memory defined to initialize module"
      in
      trace "Initializing...";
      current_module := Some (Eval.init m mem)
    | Invoke (i, es) ->
      trace "Invoking...";
      let m = match !current_module with
        | Some m -> m
        | None -> Error.error cmd.at "no module defined to invoke"
      in
      let vs = List.map (Eval.eval m) es in
      let vs' = Eval.invoke m i vs in
      if vs' <> [] then Print.print_values vs'
  with Error.Error (at, s) ->
    trace "Error:";
    prerr_endline (Source.string_of_region at ^ ": " ^ s)

let dry_command cmd =
  match cmd.it with
  | Define m ->
    Check.check_module m;
    if !Flags.print_sig then Print.print_module_sig m
  | Memory _ | Invoke _ -> ()

let run script =
  List.iter (if !Flags.dry then dry_command else run_command) script
