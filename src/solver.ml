open Core.Std

exception Unsatisfiability_Error of string

let unsat_error msg =
  let open Errors in
  raise (Unsatisfiability_Error (error msg))

let print_map tm =
  let tl = Term.Map.to_alist tm in
  let sl = List.map tl ~f:(fun (t, l) ->
    Printf.sprintf "[%s]%s" (Logic.to_string l) (Term.to_string t)) in
  String.concat ~sep:", " sl

let get_bound_exn bound constrs var =
  let lower, upper = String.Map.find_exn constrs var in
  if bound = `Lower && Term.Map.is_empty lower then
    failwith ("lack of lower bound for variable $" ^ var)
  else if bound = `Upper && Term.Map.is_empty upper then
    Term.Map.singleton Term.Nil Logic.True
  else if bound = `Upper then upper
  else lower

let merge_bounds bound old_terms new_terms =
  let map = ref Term.Map.empty in
  let iter ~key ~data =
    let term, logic = key, data in
    let iter' ~key ~data =
      let term', logic' = key, data in
      try
        let relation = Term.seniority_exn term term' in
        let combined = Logic.combine logic logic' in
        let change = function
          | None -> Some combined
          | Some logic -> Some (Logic.Or [combined; logic]) in
        if (bound = `Upper && relation < 1) ||
           (bound = `Lower && relation > -1) then
          map := Term.Map.change !map term' change
        else
          map := Term.Map.change !map term change
      with Term.Incomparable_Terms _ -> () in
    Term.Map.iter new_terms ~f:iter' in
  if Term.Map.is_empty old_terms then new_terms
  else begin
    Term.Map.iter old_terms ~f:iter;
    let s = if bound = `Upper then "upper" else "lower" in
    Log.debugf "merged %s bounds {%s} and {%s} into {%s}"
      s (print_map old_terms) (print_map new_terms) (print_map !map);
    !map
  end

let combine_bounds bound old_terms new_terms =
  Term.Map.fold new_terms ~init:old_terms ~f:(fun ~key ~data acc ->
    Term.Map.change acc key (function
    | None -> Some data
    | Some v -> Some (Logic.combine v data)))

let rec bound_terms_exn bound constrs term logic =
  let open Term in
  match term with
  | Nil | Int _ | Symbol _ -> Term.Map.singleton term logic
  | Switch x ->
    Logic.Map.fold ~init:Term.Map.empty
      ~f:(fun ~key ~data acc ->
        let bounds = bound_terms_exn bound constrs data logic in
        let bounds = Term.Map.map
          ~f:(fun x -> Logic.combine logic (Logic.combine x key)) bounds in
          combine_bounds bound acc bounds) x
  | Var x -> get_bound_exn bound constrs x

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
      Log.debugf "%s for variable $%s to {%s}" b var (print_map terms);
      if bound = `Upper then
        Some (Term.Map.empty, terms)
      else Some (terms, Term.Map.empty)
    | Some (l, u) ->
      if bound = `Upper then
        let merged = merge_bounds bound u terms in
        Log.debugf "%s for variable $%s to {%s}" b var (print_map merged);
        Some (l, merged)
      else
        let merged = merge_bounds bound l terms in
        Log.debugf "%s for variable $%s to {%s}" b var (print_map merged);
        Some (merged, u))

let rec solve_senior depth bound in_switch context left right =
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
        let rightm = bound_terms_exn bound constrs term_right logic_right in
        let constrs = set_bound_exn (depth + 1) `Upper constrs s rightm in
        constrs, logic
      else
        let leftm = bound_terms_exn bound constrs term_left logic_left in
        let constrs = set_bound_exn (depth + 1) `Lower constrs s' leftm in
        constrs, logic
    | (Nil | Int _ | Symbol _), Var s ->
      let leftm = bound_terms_exn bound constrs term_left logic_left in
      if Poly.(bound = `Upper) then
        let rightm = bound_terms_exn bound constrs term_right logic_right in
        solve_senior_multi_exn (depth + 1) bound false context leftm rightm
      else
        let constrs = set_bound_exn (depth + 1) `Lower constrs s leftm in
        constrs, logic
    | Var s, (Nil | Int _ | Symbol _) ->
      let rightm = bound_terms_exn bound constrs term_right logic_right in
      if Poly.(bound = `Lower) then
        let leftm = bound_terms_exn bound constrs term_left logic_left in
        solve_senior_multi_exn (depth + 1) bound false context leftm rightm
      else 
        let constrs = set_bound_exn (depth + 1) `Upper constrs s rightm in
        constrs, logic
    | Switch lm, Var s ->
      let leftm = bound_terms_exn bound constrs term_left logic_left in
      if Poly.(bound = `Upper) then
        let rightm = bound_terms_exn bound constrs term_right logic_right in
        solve_senior_multi_exn (depth + 1) bound true context leftm rightm
      else
        let constrs = set_bound_exn (depth + 1) `Lower constrs s leftm in
        constrs, logic
    | Var s, Switch lm ->
      let rightm = bound_terms_exn bound constrs term_right logic_right in
      if Poly.(bound = `Lower) then
        let leftm = bound_terms_exn bound constrs term_left logic_left in
        solve_senior_multi_exn (depth + 1) bound true context leftm rightm
      else 
        let constrs = set_bound_exn (depth + 1) `Upper constrs s rightm in
        constrs, logic
    | Switch lm, Switch lm' ->
      let left_map = Term.logic_map_to_term_map lm in
      let right_map = Term.logic_map_to_term_map lm' in
      solve_senior_multi_exn (depth + 1) bound true context left_map right_map
    | t, Switch lm ->
      let left_map = Term.Map.singleton term_left logic_left in
      let right_map = Term.logic_map_to_term_map lm in
      solve_senior_multi_exn (depth + 1) bound true context left_map right_map
    | Switch lm, t ->
      let right_map = Term.Map.singleton term_right logic_right in
      let left_map = Term.logic_map_to_term_map lm in
      solve_senior_multi_exn (depth + 1) bound true context left_map right_map
    | t, t' ->
      if Int.(Term.seniority_exn t t' = -1) then
        raise (Term.Incomparable_Terms (t, t'))
      else
        context
  with Term.Incomparable_Terms (t1, t2) ->
    if in_switch then context else error t1 t2

and solve_senior_multi_exn depth bound in_switch context leftm rightm =
  Term.Map.fold leftm ~init:context ~f:(fun ~key ~data acc ->
    let term_left, logic_left = key, data in
    Term.Map.fold rightm ~init:acc ~f:(fun ~key ~data acc ->
      let term_right, logic_right = key, data in
      solve_senior depth bound in_switch acc (term_left, logic_left)
        (term_right, logic_right)))

let resolve_bound_constraints topo =
  let ctx = ref (String.Map.empty, Logic.Set.empty) in
  let apply bound (left, right) =
    List.iter ~f:(fun t ->
      let t_map = Term.Map.singleton t Logic.True in
      List.iter ~f:(fun t' ->
        let t_map' = Term.Map.singleton t' Logic.True in
        ctx := solve_senior_multi_exn 0 bound false !ctx t_map t_map'
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
