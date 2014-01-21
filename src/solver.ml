open Core.Std

exception Unsatisfiability_Error of string

let unsat_error msg =
  let open Errors in
  raise (Unsatisfiability_Error (error msg))


type context = Constr.var String.Map.t * Logic.Set.t

let add_list_constr constrs guard key =
  let open Constr in
  String.Map.change constrs key (function
  (* empty case *)
  | None -> Some {
      bounds = (Term.Map.empty, Term.Map.empty);
      typ = { record = None; choice = None; lst = Some guard }
    }
  (* error cases *)
  | Some { bounds; typ = { record = Some (Logic.True, _); choice; lst } } ->
    unsat_error (Printf.sprintf "Variable $%s can't be classified as both a 
      record and a list" key)
  | Some { bounds; typ = { choice = Some (Logic.True, _); record; lst } } ->
    unsat_error (Printf.sprintf "Variable $%s can't be classified as both a 
      record and a list" key)
  (* constraint for an existing list constraint *)
  | Some { bounds; typ = { record; choice; lst = Some b; }} ->
    let guard' =
      if Logic.(b = True || guard = True || guard = b) then guard
      else Logic.And (b, guard) in
    Some { bounds; typ = { record; choice; lst = Some guard' } }
  | Some { bounds; typ = { record; choice; lst = None } } ->
    Some { bounds; typ = { record; choice; lst = Some guard } })

let add_label_constr constrs key map guard col_typ =
  let labels = String.Map.map ~f:(fun (g, _) -> g) map in
  let open Constr in
  String.Map.change constrs key (function
  (* empty case *)
  | None -> Some {
      bounds = (Term.Map.empty, Term.Map.empty);
      typ =
        match col_typ with
        | `Choice ->
          { record = None; choice = Some (guard, labels); lst = None; }
        | `Record ->
          { record = Some (guard, labels); choice = None; lst = None; }
    }
  | Some { bounds; typ } ->
    match col_typ, typ with
    (* error cases *)
    | `Record, { choice = Some (Logic.True, _); _ }
    | `Choice, { record = Some (Logic.True, _); _ } ->
      unsat_error (Printf.sprintf "Variable $%s can't be classified as both a 
        record and a choice" key)
    | `Choice, { lst = Some Logic.True; _ } ->
      unsat_error (Printf.sprintf "Variable $%s can't be classified as both a 
        list and a choice" key)
    | `Record, { lst = Some Logic.True; _ } ->
      unsat_error (Printf.sprintf "Variable $%s can't be classified as both a 
        list and a record" key)
    (* add to existing constraints *)
    | `Choice, { choice = Some (b, lm); record; lst; } ->
      let guard' =
        if Logic.(b = True || guard = True || guard = b) then guard
        else Logic.And (b, guard) in
      Some { bounds; typ =
        { record; lst; choice = Some (guard',
        String.Map.merge labels lm ~f:(fun ~key -> function
          | `Both (l1, l2) -> Some (Logic.And (l1, l2))
          | `Left l | `Right l -> Some l)); }; }
    | `Record, { record = Some (b, lm); choice; lst; } ->
      let guard' =
        if Logic.(b = True || guard = True || b = guard) then guard
        else Logic.And (b, guard) in
      Some { bounds; typ =
        { choice; lst; record = Some (guard',
        String.Map.merge labels lm ~f:(fun ~key -> function
          | `Both (l1, l2) -> Some (Logic.And (l1, l2))
          | `Left l | `Right l -> Some l)); }; }
    | `Record, { record = None; lst; choice; } ->
      Some { bounds; typ =
        { record = Some (guard, labels); choice; lst; }}
    | `Choice, { choice = None; lst; record; } ->
      Some { bounds; typ =
        { choice = Some (guard, labels); record; lst; }})

let rec resolve_collections_exn constrs guard = function
  | [] -> constrs
  | hd :: tl ->
    let fold_map constrs map = String.Map.fold ~init:constrs
      ~f:(fun ~key ~data acc ->
        let (g, t) = data in
        if Logic.(g = False) then acc
        else if Logic.(g = True) then resolve_collections_exn acc guard [t]
        else if Logic.(guard = True || guard = g) then
          resolve_collections_exn acc g [t]
        else
          resolve_collections_exn acc (Logic.And (guard, g)) [t]
        ) map in
    let open Term in
    let constrs' = match hd with
    | Nil | Int _ | Symbol _ | Var _ -> constrs
    | Tuple x -> resolve_collections_exn constrs guard x
    | Switch tl ->
      Logic.Map.fold ~init:constrs
        ~f:(fun ~key ~data acc ->
          if Logic.(guard = True || guard = key) then
            resolve_collections_exn acc key [data]
          else
            resolve_collections_exn acc (Logic.And (guard, key))  [data]
        ) tl
    | Choice (map, v) ->
      let constrs =
        match v with
        | Some v -> add_label_constr constrs v map guard `Choice
        | None -> constrs in
      fold_map constrs map
    | Record (map, v) ->
      let constrs =
        match v with
        | Some v -> add_label_constr constrs v map guard `Record
        | None -> constrs in
      fold_map constrs map
    | List (l, v) ->
      let constrs =
        match v with
        | Some v -> add_list_constr constrs guard v
        | None -> constrs in
      resolve_collections_exn constrs guard l in
    resolve_collections_exn constrs' guard tl

let set_collection_constrs_exn topo =
  let terms = List.fold ~init:[]
    ~f:(fun acc (left, right) -> acc @ left @ right) topo in
  resolve_collections_exn String.Map.empty Logic.True terms

let get_bound_exn bound constrs x =
  let cstr = String.Map.find_exn constrs x in
  let open Constr in
  let low, up = cstr.bounds in
  if Poly.(bound = `Lower) then low else up

let rec bounding_term_exn bound constrs term =
  let open Term in
  let all_variants map =
    let f acc tm =
      let l = Term.Map.to_alist tm in
      if List.is_empty acc then List.map ~f:(fun x -> [x]) l
      else
        let res = ref [] in
        List.iter
          ~f:(fun x -> res := !res @ (List.map ~f:(fun xl -> xl @ [x]) acc)) l;
        !res in
    List.fold_left ~init:[] ~f map in
  match term with
  (* the case when [], {} [nil, nil], etc. are treated as nil *)
  | t when Poly.(Term.is_nil t = Some true) ->
    Term.Map.singleton Term.Nil Logic.True
  | Nil | Int _ | Symbol _ -> Term.Map.singleton term Logic.True
  | Var x -> get_bound_exn bound constrs x
  | Tuple x ->
    let map_list = List.map ~f:(bounding_term_exn bound constrs) x in
    let r = all_variants map_list in
    let result = List.map ~f:(fun lst ->
      let g = List.fold_left ~init:Logic.True
        ~f:(fun acc (_, g) ->
          if Logic.(acc = True || acc = g) then g
          else if Logic.(g = True) then acc
          else Logic.And (g, acc)) lst in
      let t = List.map ~f:(fun (t, _) -> t) lst in
      (Term.Tuple t, g)) r in
    Term.Map.of_alist_exn result
  | List (x, tail) ->
    let map_list = List.map ~f:(bounding_term_exn bound constrs) x in
    let tl = match tail with
    | None -> Term.Map.empty 
    | Some var -> bounding_term_exn bound constrs (Var var) in
    let map_list_tl = Term.Map.fold ~init:[]
      ~f:(fun ~key ~data acc ->
        match key with
        | List (l, None) ->
          acc @ [List.map ~f:(bounding_term_exn bound constrs) l]
        | _ -> acc
      ) tl in
    let combinations = List.map ~f:(fun x -> map_list @ x) map_list_tl in
    let comb = List.fold_left ~init:[] ~f:(fun acc x -> acc @ all_variants x)
      combinations in
    List.fold_left ~init:Term.Map.empty
      ~f:(fun acc l ->
        let log, term = List.fold_left ~init:(Logic.True, [])
          ~f:(fun (lacc, tacc) (t, l) -> (Logic.combine lacc l), tacc @ [t])
          l in
        Term.Map.add ~key:(Term.List (term, None)) ~data:log acc)
      comb
  | Switch map ->
    Logic.Map.fold ~init:Term.Map.empty
      ~f:(fun ~key ~data acc -> Term.Map.add ~key:data ~data:key acc) map

let set_bound_exn depth bound constrs var term_map =
  let module SS = String.Set in
  let module SM = String.Map in
  let simplify t =
    let t = Term.canonize t in
    if Term.is_nil_exn t then Term.Nil else t in
  let term_map = Term.Map.fold ~init:Term.Map.empty
    ~f:(fun ~key ~data acc -> Term.Map.add ~key:(simplify key) ~data acc)
    term_map in

  (* add collection constraints *)
  let constrs =
    let open Term in
    Term.Map.fold ~init:constrs ~f:(fun ~key ~data acc ->
      match key with
      | List _ -> add_list_constr constrs data var
      | Record _ -> add_label_constr constrs var SM.empty data `Record
      | Choice _ -> add_label_constr constrs var SM.empty data `Choice
      | Switch _ (* will be processed recursively later *)
      | Nil | Int _ | Symbol _ | Tuple _ | Var _ -> constrs) term_map in
  let open Constr in
  let b =
    if Poly.(bound = `Upper) then
      (String.make (depth + 1) ' ') ^ "setting least upper bound"
    else (String.make (depth + 1) ' ') ^ "setting greatest lower bound" in
  let resolve_bound term guard v =
    match bound, v, term with
    (* no constraints yet *)
    | `Lower, None, t ->
      Log.debugf "%s for variable $%s to %s" b var (Term.to_string Term.Nil);
      Some {
        bounds =
          (Term.Map.singleton t guard, Term.Map.singleton Term.Nil Logic.True);
        typ = { record = None; choice = None; lst = None; };
      }
    | `Upper, None, t ->
      Log.debugf "%s for variable $%s to %s" b var (Term.to_string Term.Nil);
      Some {
        bounds =
          (Term.Map.empty, Term.Map.singleton t guard);
        typ = { record = None; choice = None; lst = None; };
      }
    | `Lower, Some ({bounds = (lb, ub); typ } as el), _ ->
      Log.debugf "%s for variable $%s to %s" b var (Term.to_string term);
      Some {el with bounds = (Term.Map.add ~key:term ~data:guard lb, ub)}
    | `Upper, Some ({bounds = (lb, ub); typ } as el), _ ->
      Log.debugf "%s for variable $%s to %s" b var (Term.to_string term);
      Some {el with bounds = (lb, Term.Map.add ~key:term ~data:guard ub)} in
  Term.Map.fold ~init:constrs
    ~f:(fun ~key ~data acc -> String.Map.change acc var (resolve_bound key
    data))
    term_map

let solve_senior_exn depth bound context left right guard =
  let cstr = [left], [right] in
  Log.debugf "%sresolving %s for constraint %s" (String.make depth ' ')
    (if bound = `Upper then "least upper bound" else "greatest lower bound")
    (Constr.to_string cstr);
  let error t1 t2 =
    unsat_error
      (Printf.sprintf "the seniority relation %s <= %s does not hold"
        (Term.to_string t1)
        (Term.to_string t2)) in
  try
    let open Term in
    let constrs, logic = context in
    let constrs' =
      match left, right with
      | Var t, Var t' ->
        if Poly.(bound = `Upper) then
          let bound_term = bounding_term_exn `Upper constrs right in
          set_bound_exn depth `Upper constrs t bound_term guard
        else
          let bound_term = bounding_term_exn `Lower constrs left in
          set_bound_exn depth `Lower constrs t' bound_term guard
(*
      | (Nil | Int _ | Symbol _ | Tuple _ | List _ | Record _ | Choice _),
        Var t ->
        if Poly.(bound = `Upper) then
          let bounds = bounding_term_exn `Upper constrs right in
          let constrs = Term.Map.fold ~init:constrs
            ~f:(fun ~key ~data acc -> solve

*)
    in constrs', logic


let resolve_bound_constraints context topo =
  let ctx = ref context in
  let apply bound (left, right) =
    List.iter ~f:(fun t -> List.iter
        ~f:(fun t' -> ctx := solve_senior_exn 0 bound !ctx t t')
        right
      ) left in
  Log.debugf "setting least upper bounds for constraints";
  List.iter ~f:(apply `Upper) (List.rev topo);
  Log.debugf "setting greatest lower bounds for constraints";
  List.iter ~f:(apply `Lower) topo;
  !ctx



let unify_exn (g, logic) =
  Log.debugf "creating a traversal order for constraints";
  let topo = Network.traversal_order g in
  Log.debugf "setting constraints on the type of constraint";
  let constrs = set_collection_constrs_exn topo in
  constrs, logic
