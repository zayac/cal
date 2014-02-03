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
  let print_map tm =
    let tl = Term.Map.to_alist tm in
    let sl = List.map tl ~f:(fun (t, l) ->
      Printf.sprintf "[%s]%s" (Logic.to_string l) (Term.to_string t)) in
    String.concat ~sep:", " sl in 
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
      Log.debugf "%s for variable $%s to %s" b var (print_map terms);
      if bound = `Upper then
        Some (Term.Map.empty, terms)
      else Some (terms, Term.Map.empty)
    | Some (l, u) ->
      if bound = `Upper then
        let merged = merge_bounds bound u terms in
        Log.debugf "%s for variable $%s to %s" b var (print_map merged);
        Some (l, merged)
      else
        let merged = merge_bounds bound l terms in
        Log.debugf "%s for variable $%s to %s" b var (print_map merged);
        Some (merged, u))

let map_to_switch map =
  let logic_map =
    Term.Map.fold ~init:Logic.Map.empty
      ~f:(fun ~key ~data acc ->
        if Logic.Map.mem acc data then
          failwith "logical key duplication"
        else
          Logic.Map.add acc ~key:data ~data:key)
      map in
  Term.Switch logic_map

let switch_to_map term =
  Logic.Map.fold ~init:Term.Map.empty
    ~f:(fun ~key ~data acc ->
      Term.Map.change acc data (function
        | None -> Some key
        | Some v -> Some (Logic.Or [v; key])))
    term

let bounds_of_switch bound constrs lm =
  Logic.Map.fold ~init:Term.Map.empty
    ~f:(fun ~key ~data acc ->
      let b = bound_terms_exn bound constrs data in
      let b = Term.Map.map ~f:(fun v -> Logic.And (v, key)) b in
      merge_bounds bound acc b)
  lm

(*
let rec solve_senior_exn depth bound context leftm rightm =
  let error t1 t2 =
    unsat_error
      (Printf.sprintf "the seniority relation %s <= %s does not hold"
        (Term.to_string t1)
        (Term.to_string t2)) in
  try
    let open Term in
    let constrs, logic = context in
    match left, right with
    | Var t, (Nil | Int _ | Symbol _) ->
      if Poly.(bound = `Upper) then
        let term_map = bound_terms_exn `Upper constrs right in
        let constrs = set_bound_exn depth `Upper constrs t term_map in
        constrs, logic
      else
        let term_map = bound_terms_exn `Upper constrs left in
        solve_senior_exn (depth + 1) `Lower context (map_to_switch term_map)
          right
    | (Nil | Int _ | Symbol _), Var t ->
      if Poly.(bound = `Lower) then
        let term_map = bound_terms_exn `Upper constrs left in
        let constrs = set_bound_exn depth `Lower constrs t term_map in
        constrs, logic
      else
        let term_map = bound_terms_exn `Upper constrs left in
        solve_senior_exn (depth + 1) `Upper context left
          (map_to_switch term_map)
    | Var t, Switch lm ->
      if Poly.(bound = `Upper) then
        let bounds = bounds_of_switch `Upper constrs lm in
        let constrs = set_bound_exn depth `Upper constrs t bounds in
        constrs, logic
      else
        let bounds = bounds_of_switch `Upper constrs lm in
        solve_senior_exn (depth + 1) bound context (map_to_switch bounds) right
    | Switch lm, Var t ->
      if Poly.(bound = `Lower) then
        let bounds = bounds_of_switch `Upper constrs lm in
        let constrs = set_bound_exn depth `Lower constrs t bounds in
        constrs, logic
      else
        let bounds = bounds_of_switch `Upper constrs lm in
        solve_senior_exn (depth + 1) bound context left (map_to_switch bounds)
    | (Nil | Int _ | Symbol _), (Nil | Int _ | Symbol _) ->
      if Int.(Term.seniority_exn left right = -1) then error left right
      else context
  with Term.Incomparable_Terms (t1, t2) -> error t1 t2

*)
(*

let solve_senior_exn depth bound (constrs, logic) left_term left_logic
  right_term right_logic =
  match left_term, right_term
  | 

*)

let extract_vars tm =
  Term.Map.fold ~init:(String.Map.empty, Term.Map.empty)
    ~f:(fun ~key ~data (vars, terms) ->
      match key with
      | Term.Var x -> String.Map.add vars ~key:x ~data, terms
      | t -> vars, Term.Map.add terms ~key ~data) tm

let solve_senior_multi_exn depth bound context leftm (rightm : Logic.t Term.Map.t)=
  let constrs, logic = context in
  if bound = `Upper then
    let vars, terms = extract_vars leftm in
    (* ground terms in the right part *)
    let terms' = Term.Map.fold ~init:Term.Map.empty
      ~f:(fun ~key ~data acc ->
        let bounds = bound_terms_exn bound constrs key in
        merge_bounds bound acc bounds) rightm in
    (* set bounds for variables in the left part *)
    let constrs =
      String.Map.fold ~init:constrs
        ~f:(fun ~key ~data acc ->
          set_bound_exn (depth + 1) `Upper constrs key terms') vars in
    let logic' = Term.logic_seniority_exn terms terms' in
    constrs, logic'
  else
    let vars, terms = extract_vars rightm in
    (* ground terms in the left part *)
    let terms' = Term.Map.fold ~init:Term.Map.empty
      ~f:(fun ~key ~data acc ->
        let bounds = bound_terms_exn bound constrs key in
        merge_bounds bound acc bounds) leftm in
    (* set bounds for variables in the right part *)
    let constrs =
      String.Map.fold ~init:constrs
        ~f:(fun ~key ~data acc ->
          set_bound_exn (depth + 1) `Lower constrs key terms') vars in
    let logic' = Term.logic_seniority_exn terms' terms in
    constrs, logic'

    
(*
  let apply ~key ~data context =
    let term, logic = key, data in
    Term.Map.fold ~init:context
      ~f:(fun ~key ~data acc -> solve_senior_exn depth bound context term logic
        key data)
      rightm in
  Term.Map.fold ~init:context ~f:apply leftm

*)
let resolve_bound_constraints topo =
  let ctx = ref (String.Map.empty, Logic.Set.empty) in
  let apply bound (left, right) =
    List.iter ~f:(fun t ->
      let t_map = Term.Map.singleton t Logic.True in
      List.iter ~f:(fun t' ->
        let t_map' = Term.Map.singleton t' Logic.True in
        ctx := solve_senior_multi_exn 0 bound !ctx t_map t_map'
        ) right
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
