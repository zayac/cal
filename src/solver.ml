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

let merge_bounds bound old_terms new_terms =
  Term.Map.fold new_terms ~init:old_terms ~f:(fun ~key ~data acc ->
    Term.Map.change acc key (function
    | None -> Some data
    | Some value -> Some (Logic.combine value data)))
(*
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
*)

let rec bound_terms_exn bound constrs term =
  let open Term in
  match term with
  | Nil | Int _ | Symbol _ -> Term.Map.singleton term Logic.True
  | Switch x ->
    Logic.Map.fold ~init:Term.Map.empty
      ~f:(fun ~key ~data acc ->
        let bounds = bound_terms_exn bound constrs data in
        let bounds = Term.Map.map ~f:(fun x -> Logic.combine x key) bounds in
        merge_bounds bound acc bounds) x
  | Var x -> get_bound_exn bound constrs x

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

let switch_clauses = ref (Stack.create ())

let rec solve_senior depth bound in_switch sol context left right =
  let constrs, logic = context in
  let term_left, logic_left = left in
  let term_right, logic_right = right in
  let open Term in
  let error t1 t2 =
    unsat_error
      (Printf.sprintf "the seniority relation %s <= %s does not hold"
        (Term.to_string t1)
        (Term.to_string t2)) in
  try
    match term_left, term_right with
    | Var s, Var s' ->
      if Poly.(bound = `Upper) then
        let rightm = bound_terms_exn bound constrs term_right in
        let constrs = set_bound_exn (depth + 1) `Upper constrs s rightm in
        sol := Logic.combine logic_left logic_right :: !sol;
        constrs, logic
      else
        let leftm = bound_terms_exn bound constrs term_left in
        let constrs = set_bound_exn (depth + 1) `Lower constrs s' leftm in
        sol := Logic.combine logic_left logic_right :: !sol;
        constrs, logic
    | (Nil | Int _ | Symbol _), Var s ->
      let leftm = Term.Map.singleton term_left logic_left in
      if Poly.(bound = `Upper) then
        let rightm = bound_terms_exn bound constrs term_right in
        solve_senior_multi_exn (depth + 1) bound in_switch sol context leftm
          rightm
      else 
        let constrs = set_bound_exn (depth + 1) `Lower constrs s leftm in
        sol := Logic.combine logic_left logic_right :: ! sol;
        constrs, logic
    | Var s, (Nil | Int _ | Symbol _) ->
      let rightm = Term.Map.singleton term_right logic_right in
      if Poly.(bound = `Lower) then
        let leftm = bound_terms_exn bound constrs term_left in
        solve_senior_multi_exn (depth + 1) bound in_switch sol context leftm
          rightm
      else 
        let constrs = set_bound_exn (depth + 1) `Upper constrs s rightm in
        sol := Logic.combine logic_left logic_right :: !sol;
        constrs, logic
    | Switch lm, Switch lm' ->
      let left_map = Term.logic_map_to_term_map lm in
      let right_map = Term.logic_map_to_term_map lm' in
      solve_senior_multi_exn (depth + 1) bound true sol context left_map
        right_map
    | t, Switch lm ->
      let left_map = Term.Map.singleton term_left logic_left in
      let right_map = Term.logic_map_to_term_map lm in
      solve_senior_multi_exn (depth + 1) bound true sol context left_map
        right_map
    | Switch lm, t ->
      let right_map = Term.Map.singleton term_right logic_right in
      let left_map = Term.logic_map_to_term_map lm in
      solve_senior_multi_exn (depth + 1) bound true sol context left_map
        right_map
    | t, t' ->
      if Int.(Term.seniority_exn t t' = -1) then
        raise (Term.Incomparable_Terms (t, t'))
      else
        sol := Logic.combine logic_left logic_right :: !sol;
        context
  with Term.Incomparable_Terms (t1, t2) ->
    if not (in_switch) then error t1 t2
    else
      constrs,
      Logic.Set.add logic (Logic.Not (Logic.And (logic_left, logic_right)))

and solve_senior_multi_exn depth bound in_switch sol context leftm rightm =
  let sol = ref [] in
  let c, l = Term.Map.fold leftm ~init:context ~f:(fun ~key ~data acc ->
    let term_left, logic_left = key, data in
    Term.Map.fold rightm ~init:acc ~f:(fun ~key ~data acc ->
      let term_right, logic_right = key, data in
      solve_senior depth bound in_switch sol acc (term_left, logic_left)
        (term_right, logic_right))) in
  if List.is_empty !sol then c, l
  else c, Logic.Set.add l (Logic.Or !sol)

      
let resolve_bound_constraints topo =
  let ctx = ref (String.Map.empty, Logic.Set.empty) in
  let apply bound (left, right) =
    List.iter ~f:(fun t ->
      let t_map = Term.Map.singleton t Logic.True in
      List.iter ~f:(fun t' ->
        let t_map' = Term.Map.singleton t' Logic.True in
        let sol = ref [] in
        let c, l = solve_senior_multi_exn 0 bound false sol !ctx t_map t_map' in
        if List.is_empty !sol then ctx := c, l
        else ctx := c, Logic.Set.add l (Logic.Or !sol) 
        ) right
      ) left in
  Log.infof "setting least upper bounds for constraints";
  List.iter ~f:(apply `Upper) (List.rev topo);
  Log.infof "setting greatest lower bounds for constraints";
  List.iter ~f:(apply `Lower) topo;
  !ctx

let unify_exn g =
  Log.debugf "creating a traversal order for constraints";
  let topo = Network.traversal_order g in
  resolve_bound_constraints topo
