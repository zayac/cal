open Core.Std

exception Unsatisfiability_Error of string

let unsat_error msg =
  let open Errors in
  raise (Unsatisfiability_Error (error msg))

(* all boolean constraints are put here in order to be resolved later *)
let boolean_constrs = ref Constr.Set.empty

(* a shorthand to add a new boolean constraint *)
let add_bool_constr t = boolean_constrs := Constr.Set.add !boolean_constrs t

let add_list_cstr_exn cstrs key =
  let open Constr in
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
  let open Constr in
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
  let open Constr in
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

let unwrap_record_exn =
  let open Term in
  function
  | Record (h, v) -> h, v
  | Nil -> String.Map.empty, None
  | _ -> invalid_arg "record as a term is expected"

let unwrap_choice_exn =
  let open Term in
  function
  | Choice (h, v) -> h, v
  | Nil -> String.Map.empty, None
  | _ -> invalid_arg "record as a term is expected"

type bound =
  | UpperB
  | LowerB

type map_type =
  | RecordMap
  | ChoiceMap

let get_bound_exn bound constrs x =
  let cstr = String.Map.find_exn constrs x in
  let open Constr in
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

let rec bounding_map_exn bound constrs mtype x tl =
  let module SM = String.Map in
  let f ~key ~data:(g, t) map =
    SM.add map ~key ~data:(bounding_term_exn bound constrs g,
      bounding_term_exn bound constrs t) in
  let map = SM.fold ~init:SM.empty ~f x in
  let map = match tl with
  | None -> map
  | Some var ->
    let tlrec = get_bound_exn bound constrs var in
    let tail = if mtype = RecordMap then get_record_term_exn tlrec
      else get_choice_term_exn tlrec in
    SM.fold ~init:map ~f:(fun ~key ~data acc -> SM.add ~key ~data acc) tail in
  if mtype = RecordMap then Term.Record (map, None)
  else Term.Choice (map, None)

and  bounding_term_exn bound constrs term =
  let open Term in
  match term with
  (* the case when [], {} [nil, nil], etc. are treated as nil *)
  | t when Poly.(Term.is_nil t = Some true) -> Nil
  | Nil | Int _ | Symbol _ -> term
  | Var x -> get_bound_exn bound constrs x
  | Tuple x -> Tuple (List.map ~f:(bounding_term_exn bound constrs) x)
  | List (x, tail) ->
    let tl = match tail with
    | None -> []
    | Some var ->
      get_list_term_exn (bounding_term_exn bound constrs (Var var)) in
    List ((List.map ~f:(bounding_term_exn bound constrs) x) @ tl, None)
  | Record (x, tl) -> bounding_map_exn bound constrs RecordMap x tl
  | Choice (x, tl) -> bounding_map_exn bound constrs ChoiceMap x tl

let verify_collection_exn var col term f =
  let open Constr in
  let open Term in
  match col, term with
  | None, _
  | _, Nil
  | Some (RecordWoLabels _), Record _
  | Some (ChoiceWoLabels _), Choice _
  | Some ListCol, List _ -> f
  | _ -> unsat_error ("constraint violation for variable $" ^ var)

let set_bound_exn depth bound constrs var term =
  let module SS = String.Set in
  let module SM = String.Map in
  let term = Term.canonize term in
  let term = if Term.is_nil_exn term then Term.Nil else term in
  (* add collection constraints *)
  let constrs =
    let open Term in
    match term with
    | List _ -> add_list_cstr_exn constrs var
    | Record _ -> add_record_cstr_exn constrs var SS.empty
    | Choice _ -> add_choice_cstr_exn constrs var SS.empty
    | Nil | Int _ | Symbol _ | Tuple _ | Var _ -> constrs in
  (* satisfy collection constraints *)
  let open Constr in
  let term = match SM.find constrs var with
  | None -> term
  | Some x -> match term, x.collection with
    | Term.Record (x, None), Some (RecordWoLabels set) ->
      if Poly.(bound = LowerB) then
        Term.Record (SS.fold ~init:x ~f:SM.remove set, None)
      else if not (SS.is_empty (SS.inter set (SS.of_list (SM.keys x)))) then
        unsat_error (Printf.sprintf "constraint violation: variable $%s must \
          be a record without labels {%s}" var
          (String.concat ~sep:", " (SS.to_list set)))
      else term
    | Term.Choice (x, None), Some (ChoiceWoLabels set) ->
      if Poly.(bound = UpperB) then
        Term.Choice (SS.fold ~init:x ~f:SM.remove set, None)
      else if not (SS.is_empty (SS.inter set (SS.of_list (SM.keys x)))) then
        unsat_error (Printf.sprintf "constraint violation: variable $%s must \
          be a choice without labels {%s}" var
          (String.concat ~sep:", " (SS.to_list set)))
      else term
    | _ -> term in
  let b = if Poly.(bound = UpperB) then
    (String.make (depth + 1) ' ') ^ "setting least upper bound"
    else (String.make (depth + 1) ' ') ^ "setting greatest lower bound" in
  String.Map.change constrs var (fun v ->
    match bound, v, term with
    (* no constraints yet *)
    | LowerB, None, t ->
      LOG "%s for variable $%s to %s" b var (Term.to_string Term.Nil)
      LEVEL TRACE;
      Some { bounds = (Some t, Some Term.Nil); collection = None }
    | UpperB, None, t ->
      LOG "%s for variable $%s to %s" b var (Term.to_string Term.Nil)
        LEVEL TRACE;
      Some { bounds = (None, Some t); collection = None }
    (* the greatest lowest bound is not set yet *)
    | LowerB, (Some ({ bounds = (None, ub); collection = col } as el)), _ ->
      LOG "%s for variable $%s to %s" b var (Term.to_string term) LEVEL TRACE;
      verify_collection_exn var col term
        (Some {el with bounds = (Some term, ub)})
    (* the greatest lowest bound exists (try to shrink) *)
    | LowerB, ((Some { bounds = (Some oldt, ub); collection = col}) as el),
        newt ->
      verify_collection_exn var col term
        (if Poly.(Term.seniority_exn oldt newt = 1) then begin
          LOG "%s for variable $%s to %s" b var (Term.to_string newt)
            LEVEL TRACE;
          Some { bounds = (Some newt, ub); collection = col }
         end else el
        )
    (* the least upper bound is not set yet *)
    | UpperB, (Some ({ bounds = (lb, None); collection = col } as el)), _ ->
      LOG "%s for variable $%s to %s" b var (Term.to_string term) LEVEL TRACE;
      verify_collection_exn var col term
        (Some {el with bounds = (lb, Some term)})
    (* the least upper bound exists (try to shrink) *)
    | UpperB, ((Some { bounds = (lb, Some oldt); collection = col}) as el),
        newt ->
      verify_collection_exn var col term
        (if Poly.(Term.seniority_exn newt oldt = 1) then begin
          LOG "%s for variable $%s to %s" b var (Term.to_string newt)
            LEVEL TRACE;
           Some { bounds = (lb, Some newt); collection = col}
         end else el
        )
  )

let map_to_nil_exn depth bound constrs h v =
  let open Term in
  let verify ~key ~data constrs = match data with
  | Var t, Var t' ->
    let constrs = set_bound_exn depth bound constrs t Nil in
    set_bound_exn depth bound constrs t' Nil
  | Var t, (Nil | Int _ | Symbol _ | Tuple _ | List _ | Record _ | Choice _)
  | (Nil | Int _ | Symbol _ | Tuple _ | List _ | Record _ | Choice _), Var t ->
    set_bound_exn depth bound constrs t Nil
  | (Nil | Int _ | Symbol _ | Tuple _ | List _ | Record _ | Choice _),
    (Nil | Int _ | Symbol _ | Tuple _ | List _ | Record _ | Choice _) ->
    constrs in
  let constrs = match v with
  | None -> constrs
  | Some t -> set_bound_exn depth bound constrs t Nil in
  String.Map.fold ~init:constrs ~f:verify h

(* solve seniority relation for record and choice *)
let rec solve_map_exn depth bound constrs mtype left right =
  let module SM = String.Map in
  let module SS = String.Set in
  let (r, v), (r', v') =
    if mtype = RecordMap then
      unwrap_record_exn left, unwrap_record_exn right
    else unwrap_choice_exn left, unwrap_choice_exn right in
  (* resolve terms that are associated with same labels in both maps.
     E.g. from { a, b, c, d | $x } and { b, c, e, f | $y }, terms with labels b
     and c will be removed. *)
  let set, set' = SS.of_list (SM.keys r), SS.of_list (SM.keys r') in
  let solve constrs l =
    let (t1, t2), (t1', t2') = SM.find_exn r l, SM.find_exn r' l in
    let constrs =
      solve_senior_exn (depth + 1) bound constrs t1 t1' in
    solve_senior_exn (depth + 1) bound constrs t2 t2' in
  let constrs =
    SS.fold ~init:constrs ~f:solve (SS.inter set set') in
  let set, set' = SS.diff set set', SS.diff set' set in
  (* In records (choices) all labels are specified in the right (left) term
     must be also present in the left (right) term, otherwise this is an error.
     E.g. {a, b, c, d} <= {a, b, c, e | $x } -- left term lacks e
     (: a, b, c, e | $x :) <= (: a, b, c, d :) -- right term lacks e. *)
  let _ = if (mtype = RecordMap && v = None && not (SS.is_empty set') ||
    (mtype = ChoiceMap && v' = None && not (SS.is_empty set))) then
    let ts1, ts2 = Term.to_string left, Term.to_string right in
    let ts1, ts2 = if mtype = RecordMap then ts1, ts2 else ts2, ts1 in
    unsat_error (Printf.sprintf "term %s contains labels that are not \
      presentedin term %s" ts2 ts1) in
  let from_set, from_map, from_var, to_map, to_var =
    if bound = LowerB then set, r, v, r', v' else set', r', v', r, v in
  let apply to_var =
    let tail_map = SM.empty in
    let set_tail_var tail_map l =
      let (t1, t2) = SM.find_exn from_map l in
      SM.add tail_map l (bounding_term_exn UpperB constrs t1,
        bounding_term_exn UpperB constrs t2) in
    let tail_map = SS.fold ~init:tail_map ~f:set_tail_var from_set in
    (* The content of one variable is copied to another. *)
    let apply' from_var =
      let unwrap = if mtype = RecordMap then get_record_term_exn
        else get_choice_term_exn in
      let add ~key ~data tail_map =
        if not (SM.mem to_map key) then
          SM.add tail_map ~key ~data
        else tail_map in
      SM.fold ~init:tail_map ~f:add
        (unwrap (bounding_term_exn UpperB constrs (Term.Var from_var))) in
    let tail_map = Option.value_map ~default:tail_map ~f:apply' from_var in
    if mtype = RecordMap then
      set_bound_exn depth bound constrs to_var (Term.Record (tail_map, None))
    else
      set_bound_exn depth bound constrs  to_var (Term.Choice (tail_map, None)) in
  Option.value_map ~default:constrs ~f:apply to_var

and solve_senior_exn depth bound constrs left right =
  LOG "%sresolving %s for constraint %s" (String.make depth ' ')
    (if bound = UpperB then "least upper bound" else "greatest lower bound")
    (Constr.to_string ([left], [right])) LEVEL TRACE;
  let error t1 t2 =
    unsat_error
      (Printf.sprintf "the seniority relation %s <= %s does not hold"
        (Term.to_string t1)
        (Term.to_string t2)) in
  let left, right = Equations.union left, Equations.union right in
  try
    let open Term in
    match left, right with
    | Var t, Var t' ->
      if Poly.(bound = UpperB) then
        let bound_term = bounding_term_exn UpperB constrs right in
        let constrs = set_bound_exn depth bound constrs t bound_term in
        let open Constr in
        match String.Map.find constrs t' with
        | None -> constrs
        | Some cstr -> match cstr.collection with
          | None -> constrs
          | Some (RecordWoLabels s) -> add_record_cstr_exn constrs t s
          | Some (ChoiceWoLabels s) -> add_choice_cstr_exn constrs t s
          | Some ListCol -> add_list_cstr_exn constrs t
      else begin
        let bound_term = bounding_term_exn UpperB constrs left in
        let constrs = set_bound_exn depth bound constrs t' bound_term in
        let open Constr in
        match String.Map.find constrs t with
        | None -> constrs
        | Some cstr -> match cstr.collection with
          | None -> constrs
          | Some (RecordWoLabels s) -> add_record_cstr_exn constrs t' s
          | Some (ChoiceWoLabels s) -> add_choice_cstr_exn constrs t' s
          | Some ListCol -> add_list_cstr_exn constrs t'
      end
    | (Nil | Int _ | Symbol _ | Tuple _ | List _ | Record _ | Choice _),
      Var t ->
      if Poly.(bound = UpperB) then
        solve_senior_exn (depth + 1) bound constrs left
          (bounding_term_exn UpperB constrs right)
      else
        set_bound_exn depth bound constrs t
          (bounding_term_exn UpperB constrs left)
    | Var t,
      (Nil | Int _ | Symbol _ | Tuple _ | List _ | Record _ | Choice _) ->
      if Poly.(bound = LowerB) then
        solve_senior_exn (depth + 1) bound constrs
          (bounding_term_exn UpperB constrs left)
          right
      else
        set_bound_exn depth
          bound constrs t (bounding_term_exn UpperB constrs right)
    | Tuple t, Tuple t' when Int.(List.length t = List.length t') ->
      List.fold2_exn ~init:constrs ~f:(solve_senior_exn (depth + 1) bound) t t'
    | List (t, v), List (t', v') -> begin
      (* validate the common head of the list and return remaining elements
         (depending on lists lengths) *)
      let rec validate_head constrs l1 l2 = match l1, l2 with
      | [], _ -> constrs, [], l2
      | _, [] -> constrs, l1, []
      | hd :: tl, hd' :: tl' ->
        let cstrs = solve_senior_exn (depth + 1) bound constrs hd hd' in
        validate_head cstrs tl tl' in
      let constrs, rem1, rem2 = validate_head constrs t t' in
      (* an error if the tail of the right term is not nil *)
      let _ = if Poly.(v = None && rem2 <> [] &&
        Term.is_nil (List (rem2, None)) <> Some true) then error left right in
      (* an error if the upper bound for tail variable in the right list makes
         the right list longer then the left one. *)
      let _ = if Poly.(rem1 = [] && rem2 = [] &&
        Option.value_map ~default:false
          ~f:(fun x -> Term.is_nil
            (bounding_term_exn UpperB constrs (Var x)) <> Some true
          ) v') then
        error left right in
      let rem1, rem2, what, where =
        if Poly.(bound = LowerB) then rem1, rem2, v, v'
        else rem2, rem1, v', v in
      (* set variables in the tail of the list to Nil/[] *)
      let constrs =
        if Poly.(what = None) then
          let set_ground cstrs var =
            match var with
            | Var v -> set_bound_exn depth bound cstrs v Nil
            | Nil | Int _ | Symbol _ | Tuple _ | List _ | Record _ | Choice _ ->
              cstrs in
          List.fold_left ~init:constrs ~f:set_ground rem2
        else constrs in
      match where with
      | None -> constrs
      | Some var' ->
        let tail_list = ref [] in
        let _ = List.iter ~f:(fun el ->
            tail_list := !tail_list @ [bounding_term_exn UpperB constrs el]
          ) rem1 in
        let _ = match what with
        | None -> ()
        | Some var -> tail_list := List.append !tail_list
          (get_list_term_exn (bounding_term_exn UpperB constrs (Var var))) in
        set_bound_exn depth bound constrs var' (List (!tail_list, None))
      end
    | List (l, v), Nil ->
      if Poly.(bound = UpperB) then
        let verify constrs = function
        | Var t -> set_bound_exn depth bound constrs t Nil
        | Nil | Int _ | Symbol _ | Tuple _ | List _ | Record _
        | Choice _ -> constrs in
        let constrs = match v with
          | None -> constrs
          | Some x -> set_bound_exn depth bound constrs x Nil in
        List.fold_left ~init:constrs ~f:verify l
      else
        let constrs = List.fold_left ~init:constrs
          ~f:(fun c x -> solve_senior_exn (depth + 1) bound c x Nil) l in
        Option.value_map ~default:constrs
          ~f:(fun x -> solve_senior_exn (depth + 1) bound constrs (Var x) Nil)
          v
    | Nil, List (l, v) ->
      if Poly.(bound = LowerB) then
        let verify constrs = function
        | Var t -> set_bound_exn depth bound constrs t Nil
        | Nil -> constrs
        | t when Poly.(Term.is_nil t = Some true) -> constrs
        | Int _ | Symbol _ | Tuple _ | List _ | Record _ | Choice _ ->
          unsat_error (Printf.sprintf "list %s is not nil"
            (Term.to_string right)
          ) in
          List.fold_left ~init:constrs ~f:verify l
      else
        let constrs = List.fold_left ~init:constrs
          ~f:(fun c x -> solve_senior_exn (depth + 1) bound c Nil x) l in
        Option.value_map ~default:constrs
          ~f:(fun x -> solve_senior_exn (depth + 1) bound constrs Nil (Var x))
          v
    | Record _, Record _ ->
      solve_map_exn depth bound constrs RecordMap left right
    | Choice _, Choice _ ->
      solve_map_exn depth bound constrs ChoiceMap left right
    | Nil, Choice (h, v) when Poly.(bound = LowerB) ->
      map_to_nil_exn depth bound constrs h v
    | Nil, Record (h, v) when Poly.(bound = LowerB) ->
      map_to_nil_exn depth bound constrs h v
    | Choice (h, v), Nil when Poly.(bound = UpperB) ->
      map_to_nil_exn depth bound constrs h v
    | Record (h, v), Nil when Poly.(bound = UpperB) ->
      map_to_nil_exn depth bound constrs h v
    | t, t' ->
      if Int.(Term.seniority_exn t t' = -1) then error t t'
      else constrs
  with Term.Incomparable_Terms (t1, t2) -> error t1 t2

let resolve_bound_constraints constrs topo =
  let cstrs = ref constrs in
  let apply bound (left, right) =
    List.iter ~f:(fun t -> List.iter
        ~f:(fun t' -> cstrs := solve_senior_exn 0 bound !cstrs t t')
        right
      ) left in
  LOG "setting least upper bounds for constraints" LEVEL TRACE;
  List.iter ~f:(apply UpperB) (List.rev topo);
  LOG "setting greatest lower bounds for constraints" LEVEL TRACE;
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
  constrs
