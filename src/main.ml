open Core.Std
open Network
open Solver

let loop filename =
  try
    let constrs = In_channel.with_file filename
      ~f:(fun inx -> Parser.parse Lexer.read (Lexing.from_channel inx)) in
    let g = constrs_to_graph_exn constrs in
    let _ = unify_exn g in
    ()
  with Lexer.Syntax_Error msg
     | Errors.Parsing_Error msg
     | Network.Topology_Error msg ->
  Printf.eprintf "%s\n" msg

let command =
  Command.basic
    ~summary:"Resolve constraints from AstraKahn Term Algebra (AKTA)"
    ~readme:(fun () -> "More detailed information")
    Command.Spec.(
      empty
      +> flag "-dot-output" (optional string) ~doc:"string output network \
        graph in dot format to a file provided as the argument"
      +> anon ("filename" %:string)
    )
    (fun dot_output filename () -> loop filename)

let () =
  Command.run ~version:"0.2" ~build_info:"dev version" command

