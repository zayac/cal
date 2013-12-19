open Core.Std
open Network
open Solver

(* module for creating dot-files *)
module Dot = Graph.Graphviz.Dot(struct
  include G (* use the graph module from above *)
  let edge_attributes (_, e, _) =
    [`Label (Constr.to_string e); `Color 4711]
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let vertex_attributes _ = [`Shape `Circle]
  let vertex_name v =
    String.concat ["\""; Network.Node.to_string v; "\""]
  let default_vertex_attributes _ = [ `Style `Filled;
    `Color 0x6495ED;
    `Fontcolor 0xFFFFFF;
    `Fontsize 10;
    `Fontname "Helvetica"]
  let graph_attributes _ = []
  end)

let create_dot_output g dot_output =
  Out_channel.with_file dot_output
    ~f:(fun oc -> Dot.output_graph oc g)

let loop dot_output filename =
  try
    let constrs = In_channel.with_file filename
      ~f:(fun inx -> Parser.parse Lexer.read (Lexing.from_channel inx)) in
    let g = constrs_to_graph_exn constrs in
    let _ = Option.value_map ~default:() ~f:(create_dot_output g) dot_output in
    let _ = unify_exn g in
    ()
  with Lexer.Syntax_Error msg
     | Errors.Parsing_Error msg
     | Network.Topology_Error msg
     | Solver.Unsatisfiability_Error msg ->
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
    (fun dot_output filename () -> loop dot_output filename)

let () =
  Command.run ~version:"0.2" ~build_info:"dev version" command

