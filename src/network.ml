open Core.Std
open Log

exception Topology_Error of string

let topo_error msg =
  raise (Topology_Error (Errors.error msg))

type node =
  | Env_In
  | Env_Out
  | Internal of String.Set.t
  with sexp, compare

module Node = struct
  type t = node
  let hash = Hashtbl.hash
  let to_string = function
    | Env_In -> "env_in"
    | Env_Out -> "env_out"
    | Internal s ->
      Printf.sprintf "{%s}" (String.concat ~sep:", " (String.Set.to_list s))
  module T = struct
    type t = node with sexp, compare
  end
  include Comparable.Make(T)
end

module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(Node)(Constr)

let constr_to_edge c =
  let src, dest = Constr.get_vars c in
  (if String.Set.is_empty src then Env_In else Internal src), c,
    (if String.Set.is_empty dest then Env_Out else Internal dest)

let edge_to_constr (_, e, _) = e

(* merge vertices that contain same variables *)
let merge_vertices g =
  let g' = ref g in
  let merge = function
  | Internal v as vnode ->
    let update = function
    | Internal v' as vnode' ->
      let module SS = String.Set in
      if SS.subset v v' && not (SS.equal v v') then
        begin
          Log.debugf "merging node %s with node %s" (Node.to_string vnode) 
            (Node.to_string vnode');
          let succ_edges = G.succ_e !g' vnode in
          let pred_edges = G.pred_e !g' vnode in
          List.iter ~f:(fun (src, e, dest) ->
            g' := G.add_edge_e !g' (G.E.create (Internal v') e dest);
            g' := G.remove_edge_e !g' (src, e, dest)) succ_edges;
          List.iter ~f:(fun (src, e, dest) ->
            g' := G.add_edge_e !g' (G.E.create src e (Internal v'));
            g' := G.remove_edge_e !g' (src, e, dest)) pred_edges;
          if G.in_degree !g' (Internal v) = 0
            && G.out_degree !g' (Internal v) = 0 then
            g' := G.remove_vertex !g' (Internal v)
        end
    | Env_In | Env_Out -> () in
    G.iter_vertex update !g'
  | Env_In | Env_Out -> () in
  G.iter_vertex merge !g';
  !g'

(* check that all internal vertices (i.e. variables) are connected to either
   other vertices or the environment *)
let check_connectivity_exn g =
  let check = function
  | Internal x as vnode ->
    let module SS = String.Set in
    (* accumulate all vertices from the left and right parts of the
       neighbouring constraints *)
    let accumulate acc = List.fold_left ~init:acc
      ~f:(fun acc t -> SS.union acc (Term.get_vars t)) in
    let succ_vars = G.fold_succ_e
      (fun (_, (l, _), _) acc -> accumulate acc l) g vnode SS.empty in
    let pred_vars = G.fold_pred_e
      (fun (_, (_, r), _) acc -> accumulate acc r) g vnode SS.empty in
    if not (SS.equal succ_vars x) || not (SS.equal pred_vars x) then
      raise (topo_error "Some variables do not have bounding constraints")
  | Env_In | Env_Out -> () in
  G.iter_vertex check g

let constrs_to_graph_exn cstrs =
  let env_in_found = ref false in
  let env_out_found = ref false in
  let g = ref G.empty in
  let add c =
    let src, edge, dest = constr_to_edge c in
    if src = Env_In then env_in_found := true;
    if dest = Env_Out then env_out_found := true;
    Log.debugf "adding edge (%s, \"%s\", %s) to the graph" (Node.to_string src)
      (Constr.to_string c) (Node.to_string dest);
    g := G.add_edge_e !g (G.E.create src edge dest) in
  List.iter ~f:add cstrs;
  if not !env_in_found || not !env_out_found then
    topo_error "There are no constraints with ground terms as the source term";
  Log.debugf "merging nodes corresponding to the same set of vertices";
  g := merge_vertices !g;
  check_connectivity_exn !g;
  !g

(*
let to_acyclic g =
  let module D = Graph.Traverse.Dfs(G) in
  let module NS = Node.Set in
  let visited = ref NS.empty in
  let loops = ref Set.Poly.empty in
  let acyclic_g = ref g in
  let add_vertex v =
    let check_edge e =
      if NS.mem !visited (G.E.dst e) || Node.(G.E.src e = G.E.dst e) then
        begin
          acyclic_g := G.remove_edge_e !acyclic_g e;
          loops := Set.Poly.add !loops e
        end
      else
        visited := NS.add !visited v in
    List.iter ~f:check_edge (G.succ_e !acyclic_g v) in
  D.prefix add_vertex !acyclic_g;
  !acyclic_g, !loops
*)

let traversal_order g =
  let module T = Graph.Topological.Make_stable(G) in
  let topo = ref [] in
  let traversed = ref Node.Set.empty in
  let loops = ref [] in
  let add_edges v =
    List.iter ~f:(fun (source, x, sink) ->
      if Node.Set.mem !traversed source then begin
        Log.debugf "constraint %s is scheduled" (Constr.to_string x);
        topo := x :: !topo
      end else
        loops := x :: !loops) (G.pred_e g v);
    traversed := Node.Set.add !traversed v in
  T.iter add_edges g;
  List.iter ~f:(fun x ->
    Log.debugf "constraint %s is marked as a loop constraint"
      (Constr.to_string x)) !loops;
  List.rev !topo, List.rev !loops
