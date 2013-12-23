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
  LOG "outputting the network graph in dot format to %s" dot_output LEVEL INFO;
  Out_channel.with_file dot_output
    ~f:(fun oc -> Dot.output_graph oc g)

let print_constraints map =
  let f ~key ~data =
    let g, t = data.bounds in
    let print_term = function
    | None -> "???"
    | Some t -> Term.to_string t in
    Printf.printf "%s <= $%s <= %s\n" (print_term g) key (print_term t);
    match data.collection with
    | None -> ()
    | Some (RecordWoLabels x) ->
      let l = if String.Set.is_empty x then ""
      else
        Printf.sprintf " without labels {%s}"
        (String.concat ~sep:", " (String.Set.to_list x)) in
      Printf.printf "$%s is a record%s\n" key l
    | Some (ChoiceWoLabels x) ->
      let l = if String.Set.is_empty x then ""
      else
        Printf.sprintf " without labels {%s}"
        (String.concat ~sep:", " (String.Set.to_list x)) in
      Printf.printf "$%s is a choice%s\n" key l
    | Some ListCol -> Printf.printf "$%s is a list\n" key in
  String.Map.iter ~f map

let loop dot_output filename =
(*    let test = Term.Record (String.Map.singleton "b" (Term.Tuple [Term.Symbol "not"; Term.Nil], Term.Nil), None) in
    print_endline (Term.to_string test);
    Printf.printf "%b" (Term.is_nil_exn test); *)
  Location.filename := filename;
  try
    LOG "reading and parsing constraints from %s" filename LEVEL INFO;
    let constrs = In_channel.with_file filename
      ~f:(fun inx -> Parser.parse Lexer.read (Lexing.from_channel inx)) in
    LOG "%d constraints are parsed" (List.length constrs) LEVEL INFO;
    LOG "constructing a graph from constraints" LEVEL INFO;
    let g = constrs_to_graph_exn constrs in
    let _ = Option.value_map ~default:() ~f:(create_dot_output g) dot_output in
    LOG "unifying constraints represented as the graph" LEVEL INFO;
    let bounds = unify_exn g in
    let _ = print_constraints bounds in
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

