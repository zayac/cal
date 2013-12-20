open Core.Std

type collection_constr =
  | RecordWoLabels of String.Set.t
  | ChoiceWoLabels of String.Set.t
  | ListCol

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
    | Some ListCol -> Printf.printf "$%s is a list\n" key in
  String.Map.iter ~f map

exception Unsatisfiability_Error of string

let unsat_error msg = raise (Unsatisfiability_Error msg)

let add_list_cstr_exn cstrs key =
  LOG "variable %s must be a list" key LEVEL TRACE;
  String.Map.change cstrs key (function
    | None -> Some { bounds = (None, Some Term.Nil); collection = Some ListCol }
    | Some { bounds; collection } ->
      match collection with
      | Some (RecordWoLabels _) -> unsat_error
        (Printf.sprintf "Variable $%s can't be classified as list and \
          record at the same time" key)
      | Some (ChoiceWoLabels _) -> unsat_error
        (Printf.sprintf "Variable $%s can't be classified as list and \
          choice at the same time" key)
      | Some ListCol | None -> Some { bounds; collection = Some ListCol }
    )

let add_record_cstr_exn cstrs key labels =
  LOG "variable %s must be a record without labels {%s}" key
    (String.concat ~sep:", " (String.Set.to_list labels)) LEVEL TRACE;
  String.Map.change cstrs key (function
    | None -> Some { bounds = (None, Some Term.Nil);
      collection = Some (RecordWoLabels labels) }
    | Some { bounds; collection } ->
      match collection with
      | Some ListCol -> unsat_error
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
  LOG "variable %s must be a choice without labels {%s}" key
    (String.concat ~sep:", " (String.Set.to_list labels)) LEVEL TRACE;
  String.Map.change cstrs key (function
    | None -> Some { bounds = (None, Some Term.Nil);
      collection = Some (ChoiceWoLabels labels) }
    | Some { bounds; collection } ->
      match collection with
      | Some ListCol -> unsat_error
        (Printf.sprintf "Variable $%s can't be classified as choice and \
          list at the same time" key)
      | Some (RecordWoLabels _) -> unsat_error
        (Printf.sprintf "Variable $%s can't be classified as choice and \
          Record at the same time" key)
      | Some (ChoiceWoLabels x) -> Some { bounds;
        collection = Some (ChoiceWoLabels (String.Set.union x labels)) }
      | None -> Some { bounds; collection = Some (ChoiceWoLabels labels) }
    )

(* resolve constraints for labels and collection types *)
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

(* resolve constraints on labels and collection types given the constraint
   schedule *)
let set_collection_constrs_exn constrs =
  let terms = List.fold ~init:[] 
    ~f:(fun acc (left, right) -> acc @ left @ right) constrs in
  resolve_collections_exn String.Map.empty terms
(*
let get_list_term_exn =
  let open Term in
  function
  | List (x, _) -> x
  | Nil -> []
  | _ -> invalid_arg "list as a term is expected"

let get_record_term_exn =
  let open Term in
  function
  | Record (x, _) -> x
  | Nil -> String.Map.empty
  | _ -> invalid_arg "record as a term is expected"

let get_choice_term_exn =
  let open Term in
  function
  | Choice (x, _) -> x
  | Nil -> String.Map.empty
  | _ -> invalid_arg "record as a term is expected"
*)
type bound =
  | UpperB
  | LowerB

type map_type =
  | RecordMap
  | ChoiceMap

let rec bounding_term_exn bound constrs term =
  let open Term in
  match term with
  (* the case when [], {} [nil, nil], etc. are treated as nil *)
  | t when Poly.(Term.is_nil t = Some true) -> Nil
  | Nil | Int _ | Symbol _ -> term
  | Var x ->
    let cstr = String.Map.find_exn constrs x in
    let low, up = cstr.bounds in
    if Poly.(bound = LowerB) then
      match low with
      | None -> invalid_arg
        (Printf.sprintf "lower bound for variable $%s does not exist" x)
      | Some t -> t
    else
      begin
        match up with
        | None -> invalid_arg
          (Printf.sprintf "upper bound for variable $%s does not exist" x)
        | Some t -> t
      end
  | Tuple x -> Tuple (List.map ~f:(bounding_term_exn bound constrs) x)

let verify_collection var col term f =
  let open Term in
  match col, term with
  | None, _
  | _, Nil
  | Some (RecordWoLabels _), Record _
  | Some (ChoiceWoLabels _), Choice _
  | Some ListCol, List _ -> f
  | _ -> unsat_error ("constraint violation for variable $" ^ var)

let set_bound_exn bound constrs var term =
  let term = Term.canonize term in
  let term = if Term.is_nil_exn term then Term.Nil else term in
  String.Map.change constrs var (fun v -> match bound, v, term with
    (* no constraints yet *)
    | LowerB, None, t ->
            Some { bounds = (Some t, Some Term.Nil); collection = None }
    | UpperB, None, t ->
      Some { bounds = (None, Some t); collection = None }
    (* the greatest lowest bound for variable is already nil *)
    | LowerB, ((Some { bounds = (Some Term.Nil, ub); collection = col }) as el),
        _ ->
      verify_collection var col term el 
    (* the greatest lowest bound is not set yet *)
    | LowerB, (Some ({ bounds = (None, ub); collection = col } as el)), _ ->
      verify_collection var col term (Some {el with bounds = (Some term, ub)})
    (* the greatest lowest bound exists (try to shrink) *)
    | LowerB, ((Some { bounds = (Some oldt, ub); collection = col}) as el),
        newt ->
      verify_collection var col term
        (if Term.seniority_exn oldt newt = 1 then
           Some { bounds = (Some newt, ub); collection = col }
         else el
        )
    (* the least upper bound is not set yet *)
    | UpperB, (Some ({ bounds = (lb, None); collection = col } as el)), _ ->
      verify_collection var col term (Some {el with bounds = (lb, Some term)})
    (* the least upper bound exists (try to shrink) *)
    | UpperB, ((Some { bounds = (lb, Some oldt); collection = col}) as el),
        newt ->
      verify_collection var col term
        (if Term.seniority_exn newt oldt = 1 then
           Some { bounds = (lb, Some newt); collection = col}
         else el
        )
  )

let rec solve_senior_exn depth bound constrs left right =
  LOG "%sresolving %s for constraint %s" (String.make depth ' ')
    (if bound = UpperB then "lowest upper bound" else "greatest lower bound")
    (Constr.to_string ([left], [right])) LEVEL TRACE;
  let error t1 t2 =
    unsat_error
      (Printf.sprintf "the seniority relation %s <= %s does not hold"
        (Term.to_string t1)
        (Term.to_string t2)) in
  try
    let open Term in
    match left, right with
    | Var t, Var t' ->
      if Poly.(bound = UpperB) then
        set_bound_exn bound constrs t (bounding_term_exn UpperB constrs right)
      else
        set_bound_exn bound constrs t' (bounding_term_exn UpperB constrs left)
    | (Nil | Int _ | Symbol _ | Tuple _), Var t ->
      if Poly.(bound = UpperB) then
        solve_senior_exn (depth + 1) bound constrs left
          (bounding_term_exn UpperB constrs right)
      else
        set_bound_exn bound constrs t (bounding_term_exn UpperB constrs left)
    | Var t, (Nil | Int _ | Symbol _ | Tuple _) ->
      if Poly.(bound = LowerB) then
        solve_senior_exn (depth + 1) bound constrs
          (bounding_term_exn UpperB constrs left)
          right
      else
        set_bound_exn bound constrs t (bounding_term_exn UpperB constrs right)
    | Tuple t, Tuple t' when Int.(List.length t = List.length t') ->
      List.fold2_exn ~init:constrs ~f:(solve_senior_exn (depth + 1) bound) t t'
    | t, t' ->
      if Int.(Term.seniority_exn t t' = -1) then error t t'
      else constrs
  with Term.Incomparable_Terms (t1, t2) -> error t1 t2

let resolve_bound_constraints (constrs : var_constr String.Map.t) topo =
  let cstrs = ref constrs in
  let apply bound (left, right) =
    List.iter ~f:(fun t -> List.iter
        ~f:(fun t' -> cstrs := solve_senior_exn 0 bound !cstrs t t')
        right
      ) left in
  LOG "setting upper bounds for constraints" LEVEL TRACE;
  List.iter ~f:(apply UpperB) (List.rev topo);
  LOG "setting lower bounds for constraints" LEVEL TRACE;
  List.iter ~f:(apply LowerB) topo;
  !cstrs

let unify_exn g =
  (*let acyclic_g, loops = Network.to_acyclic g in*)
  LOG "creating a traversal order for constraints" LEVEL DEBUG;
  let topo = Network.traversal_order g in
  LOG "setting constraints on the type of constraint" LEVEL DEBUG;
  let constrs = set_collection_constrs_exn topo in
  LOG "resolving bound constraints" LEVEL DEBUG; 
  let constrs = resolve_bound_constraints constrs topo in
  print_constraints constrs;
  constrs
