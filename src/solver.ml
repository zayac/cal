open Core.Std

type collection_constr =
  | RecordWoLabels of String.Set.t
  | ChoiceWoLabels of String.Set.t
  | List

type var_constr =
  {
    bounds     : Term.t option * Term.t option;
    collection : collection_constr option;
  }

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
      Printf.printf "$%s is a record without labels {%s}\n" key
      (String.concat ~sep:", " (String.Set.to_list x))
    | Some (ChoiceWoLabels x) ->
      Printf.printf "$%s is a choice without labels {%s}\n" key
      (String.concat ~sep:", " (String.Set.to_list x))
    | Some List -> Printf.printf "$%s is a list\n" key in
  String.Map.iter ~f map

exception Unsatisfiability_Error of string

let unsat_error msg = raise (Unsatisfiability_Error msg)

let add_list_cstr_exn cstrs key =
  String.Map.change cstrs key (function
    | None -> Some { bounds = (None, None); collection = Some List }
    | Some { bounds; collection } ->
      match collection with
      | Some (RecordWoLabels _) -> unsat_error
        (Printf.sprintf "Variable $%s can't be classified as list and \
          record at the same time" key)
      | Some (ChoiceWoLabels _) -> unsat_error
        (Printf.sprintf "Variable $%s can't be classified as list and \
          choice at the same time" key)
      | Some List | None -> Some { bounds; collection = Some List }
    )

let add_record_cstr_exn cstrs key labels =
  String.Map.change cstrs key (function
    | None -> Some { bounds = (None, None);
      collection = Some (RecordWoLabels labels) }
    | Some { bounds; collection } ->
      match collection with
      | Some List -> unsat_error
        (Printf.sprintf "Variable $%s can't be classified as record and \
          list at the same time" key)
      | Some (ChoiceWoLabels _) -> unsat_error
        (Printf.sprintf "Variable $%s can't be classified as record and \
          choice at the same time" key)
      | Some (RecordWoLabels x) -> Some { bounds;
        collection = Some (RecordWoLabels (String.Set.union x labels)) }
      | None -> Some { bounds; collection = Some (RecordWoLabels labels) }
    )

let add_choice_cstr_exn cstrs key labels =
  String.Map.change cstrs key (function
    | None -> Some { bounds = (None, None);
      collection = Some (ChoiceWoLabels labels) }
    | Some { bounds; collection } ->
      match collection with
      | Some List -> unsat_error
        (Printf.sprintf "Variable $%s can't be classified as choice and \
          list at the same time" key)
      | Some (RecordWoLabels _) -> unsat_error
        (Printf.sprintf "Variable $%s can't be classified as choice and \
          Record at the same time" key)
      | Some (ChoiceWoLabels x) -> Some { bounds;
        collection = Some (ChoiceWoLabels (String.Set.union x labels)) }
      | None -> Some { bounds; collection = Some (ChoiceWoLabels labels) }
    )

let rec resolve_collections_exn constrs = function
  | [] -> constrs
  | hd :: tl ->
    let open Term in
    let module SM = String.Map in
    let set f map var =
      let labels = String.Set.of_list (SM.keys map) in
      SM.fold
        ~init:(match var with
          | None -> constrs 
          | Some x -> f constrs x labels
        )
        ~f:(fun ~key ~data acc ->
              let g, t = data in
              resolve_collections_exn (resolve_collections_exn acc [g]) [t]
        )
        map in
    let constrs' = match hd with
    | Choice (map, v) -> set add_choice_cstr_exn map v
    | Record (map, v) -> set add_record_cstr_exn map v
    | List (l, v) ->
      List.fold_left
        ~init:(match v with
          | None -> constrs
          | Some x -> add_list_cstr_exn constrs x
        )
        ~f:(fun acc x -> resolve_collections_exn acc [x])
        l
    | Tuple x ->
      List.fold_left ~init:constrs
        ~f:(fun acc x -> resolve_collections_exn acc [x]) x
    | Nil | Int _ | Symbol _ | Var _ -> constrs in
    resolve_collections_exn constrs' tl

(* creates a traversal order for constraints *) 
let schedule g =
  let topo = ref [] in
  let add_edges v =
    List.iter ~f:(fun (_, x, _) -> topo := !topo @ [x])
      (Network.G.pred_e g v) in
  Network.T.iter add_edges g;
  !topo

let set_collection_constrs_exn constrs =
  let terms = List.fold ~init:[] 
    ~f:(fun acc (left, right) -> acc @ left @ right) constrs in
  resolve_collections_exn String.Map.empty terms

let unify_exn g =
  let acyclic_g, loops = Network.to_acyclic g in
  let topo = schedule acyclic_g in
  let constrs = set_collection_constrs_exn topo in
  print_constraints constrs;
  constrs
