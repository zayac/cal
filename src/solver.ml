open Core.Std

exception Unsatisfiability_Error of string

let unsat_error msg =
  let open Errors in
  raise (Unsatisfiability_Error (error msg))

let get_bound_exn bound constrs var =
  let lower, upper = String.Map.find_exn constrs var in
  if bound = `Lower && Term.Map.is_empty lower then
    failwith ("lack of lower bound for variable $" ^ var)
  else if bound = `Upper && Term.Map.is_empty upper then
    Term.Map.singleton Term.Nil Logic.True
  else if bound = `Upper then upper
  else lower

let bound_terms_exn bound constrs term =
  let open Term in
  match term with
  | Nil | Int _ | Symbol _ -> Term.Map.singleton term Logic.True
  | Var x -> get_bound_exn bound constrs x

let merge_bounds bound old_terms new_terms =
  let fold ~key ~data acc =
    let term, logic = key, data in
    let fold' ~key ~data (term, logic, matched) =
      let term', logic' = key, data in
      try
        let relation = Term.seniority_exn term term' in
        let combined_logic = Logic.combine logic logic' in
        if bound = `Upper then
          if relation < 1 then (term, combined_logic, true)
          else (term', combined_logic, true)
        else
          if relation < 1 then (term', combined_logic, true)
          else (term, combined_logic, true)
      with Term.Incomparable_Terms _ -> (term, logic, matched) in
    let new_term, new_logic, is_matched =
      Term.Map.fold ~init:(term, logic, false) ~f:fold' new_terms in
    if is_matched then Term.Map.add ~key:new_term ~data:new_logic acc
    else acc in
  if Term.Map.is_empty old_terms then new_terms
  else Term.Map.fold ~init:Term.Map.empty ~f:fold new_terms
          
let set_bound_exn depth bound constrs var terms =
  let simplify t =
    let t = Term.canonize t in
    if Term.is_nil_exn t then Term.Nil else t in
  let terms = Term.Map.fold ~init:Term.Map.empty
    ~f:(fun ~key ~data acc -> Term.Map.add ~key:(simplify key) ~data acc)
  terms in
  let b =
    if bound = `Upper then
      (String.make (depth + 1) ' ') ^ "setting least upper bound"
    else (String.make (depth + 1) ' ') ^ "setting greatest lower bound" in
  String.Map.change constrs var (fun v ->
    match v with
    | None ->
      if bound = `Upper then
        Some (Term.Map.empty, terms)
      else Some (terms, Term.Map.empty)
    | Some (l, u) ->
      if bound = `Upper then Some (l, merge_bounds bound u terms)
      else Some (merge_bounds bound l terms, u))

let solve_senior_exn depth bound context left right = context
(*
  try
    let open Term in
    let constrs, logic = context in
    match left, right with
    | Var t, (Nil | Int _ | Symbol _) ->
      if Poly.(bound = `Upper) then
        set_bound_exn depth `Upper constrs (bound_terms_exn `Upper constrs left)

*)
let resolve_bound_constraints topo =
  let ctx = ref (String.Map.empty, Logic.Set.empty) in
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

let unify_exn g =
  Log.debugf "creating a traversal order for constraints";
  let topo = Network.traversal_order g in
  resolve_bound_constraints topo
