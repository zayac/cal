open Core.Std
open Network

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
  Log.infof "outputting the network graph in dot format to %s" dot_output;
  Out_channel.with_file dot_output
    ~f:(fun oc -> Dot.output_graph oc g)

let print_bool_constraints l =
  print_string "\nBoolean constraints:\n";
  let f x = print_endline (Logic.to_string x) in
  Logic.Set.iter ~f l

let loop dot_output debug filename =
  Location.filename := filename;
  if debug then begin
    Log.set_log_level Log.DEBUG;
    Log.set_output stdout;
  end;
  try
    Log.infof "reading and parsing constraints from %s" filename;
    let constrs, logic = In_channel.with_file filename
      ~f:(fun inx -> Parser.parse Lexer.read (Lexing.from_channel inx)) in
    Log.infof "%d constraints are parsed" (List.length constrs);
    Log.infof "constructing a graph from constraints";
    let g = constrs_to_graph_exn constrs in
    let _ = Option.value_map ~default:() ~f:(create_dot_output g) dot_output in
    Log.infof "unifying constraints represented as the graph";
    let _ = Solver.unify_exn g in
    if not (Logic.Set.is_empty logic) then
      print_bool_constraints logic
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
      +> flag "-verbose" no_arg ~doc:" print debug information"
      +> anon ("filename" %:string)
    )
    (fun dot_output debug filename () -> loop dot_output debug filename)

let () =
  Command.run ~version:"0.2" ~build_info:"dev version" command
