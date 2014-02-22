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

let merge_bounds depth bound old_terms new_terms =
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
  if Term.Map.is_empty old_terms && Term.Map.is_empty new_terms then
    Term.Map.singleton Term.Nil Logic.True
  else if Term.Map.is_empty old_terms then new_terms
  else if Term.Map.is_empty new_terms then old_terms
  else begin
    Term.Map.iter old_terms ~f:iter;
    let s = if bound = `Upper then "upper" else "lower" in
    Log.debugf "%smerged %s bounds {%s} and {%s} into {%s}"
      (String.make depth ' ') s (print_map old_terms) (print_map new_terms)
        (print_map !map);
    !map
  end

let combine_bounds bound old_terms new_terms =
  Term.Map.fold new_terms ~init:old_terms ~f:(fun ~key ~data acc ->
    Term.Map.change acc key (function
    | None -> Some data
    | Some v -> Some (Logic.combine v data)))

let rec bound_combinations = function
  | [] -> []
  | hd :: [] ->
    Term.Map.fold hd ~init:[]
      ~f:(fun ~key ~data acc -> ([key], data) :: acc)
  | hd :: tl ->
    let tail_bounds = bound_combinations tl in
    Term.Map.fold hd ~init:[]
      ~f:(fun ~key ~data acc ->
        let term, logic = key, data in
        List.fold tail_bounds ~init:acc
          ~f:(fun acc (lst, logic') ->
          (term :: lst, Logic.combine logic logic') :: acc))

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
  | Tuple x ->
    let l = List.map x ~f:(fun x -> bound_terms_exn bound constrs x logic) in
    let term_list =
      List.map (bound_combinations l) ~f:(fun (t, l) -> Tuple t, l) in
    let result = Term.Map.of_alist_exn term_list in
    result
  | List (x, s) ->
    let l = List.map x ~f:(fun x -> bound_terms_exn bound constrs x logic) in
    let term_list = bound_combinations l in
    begin
      match s with
      | None ->
        Term.Map.of_alist_exn
          (List.map term_list ~f:(fun (t, l) -> List (t, None), l))
      | Some var ->
        let bounds = bound_terms_exn bound constrs (Var var) logic in
        let lst = List.fold term_list ~init:[] ~f:(fun acc x ->
          let head, logic' = x in
          Term.Map.fold bounds ~init:acc ~f:(fun ~key ~data acc ->
            match key with
            | Term.List (l, None) ->
              (head @ l, Logic.combine logic (Logic.combine data logic'))
                :: acc
            | Term.List (l, _) ->
              raise (Unsatisfiability_Error
                (Printf.sprintf "expected a ground list term, but %s found"
                  (Term.to_string key)))
            | _ -> acc)) in
        Term.Map.of_alist_exn
          (List.map  lst ~f:(fun (t, l) -> List (t, None), l))
    end
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
      (String.make depth ' ') ^ "setting least upper bound"
    else (String.make depth ' ') ^ "setting greatest lower bound" in
    String.Map.change constrs var (fun v ->
    match v with
    | None ->
      Log.debugf "%s%s for variable $%s to {%s}" (String.make depth ' ') b var
        (print_map terms);
      if bound = `Upper then
        Some (Term.Map.empty, terms)
      else Some (terms, Term.Map.empty)
    | Some (l, u) ->
      if bound = `Upper then
        let merged = merge_bounds (depth + 1) bound u terms in
        if Term.Map.is_empty merged then
          raise (unsat_error
            (Printf.sprintf "upper bounds for variable $%s are inconsistent" 
              var))
        else
          Log.debugf "%s%s for variable $%s to {%s}" (String.make depth ' ') b
            var (print_map merged);
          Some (l, merged)
      else
        let merged = merge_bounds (depth + 1) bound l terms in
        if Term.Map.is_empty merged then
          raise (unsat_error
            (Printf.sprintf "lower bounds for variable $%s are inconsistent" 
              var))
        else
          Log.debugf "%s%s for variable $%s to {%s}" (String.make depth ' ') b
            var (print_map merged);
          Some (merged, u))

let poly_var_to_list bound context var logic_constr =
  match var with
  | None -> context, []
  | Some v ->
    let constrs, logic = context in
    let bounds = bound_terms_exn bound constrs (Term.Var v) logic_constr in
    Term.Map.fold bounds ~init:(context, [])
      ~f:(fun ~key ~data (context, acc) ->
        match key with
        | Term.List (x, None) -> context, (x, data) :: acc
        | Term.List (_, _) -> failwith "expected ground term"
        | Term.Nil -> context, acc
        | _ ->
          let constrs, logic = context in
          (constrs, Logic.Set.add logic data), acc)

let set_list_bound depth bound (c, l) v lst =
  let map = List.fold lst ~init:Term.Map.empty ~f:(fun acc (lst, logic) ->
    Term.Map.add acc ~key:(Term.List (lst, None)) ~data:logic) in
  let c = set_bound_exn (depth + 1) bound c v map in
  c, l

let rec solve_senior depth bound context left right =
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
    Log.debugf "%ssolving constraint %s <= %s" (String.make depth ' ')
      (to_string term_left) (to_string term_right);
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
    (* atomic terms *)
    | (Nil | Int _ | Symbol _), Var s ->
      let leftm = bound_terms_exn bound constrs term_left logic_left in
      if Poly.(bound = `Upper) then
        let rightm = bound_terms_exn bound constrs term_right logic_right in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else
        let constrs = set_bound_exn (depth + 1) `Lower constrs s leftm in
        constrs, logic
    | Var s, (Nil | Int _ | Symbol _) ->
      let rightm = bound_terms_exn bound constrs term_right logic_right in
      if Poly.(bound = `Lower) then
        let leftm = bound_terms_exn bound constrs term_left logic_left in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else 
        let constrs = set_bound_exn (depth + 1) `Upper constrs s rightm in
        constrs, logic
    (* tuple processing *)
    | Tuple t, Nil ->
        List.fold ~init:context ~f:(fun acc el ->
          let left = el, logic_left in
          solve_senior (depth + 1) bound acc left right) t
    | Nil, Tuple t ->
        List.fold ~init:context ~f:(fun acc el ->
          let right = el, logic_right in
          solve_senior (depth + 1) bound acc left right) t
    | Tuple t, Tuple t' when Int.(List.length t = List.length t') ->
      if Int.(List.length t = List.length t') then
        List.fold2_exn t t' ~init:context
          ~f:(fun context t t' ->
            let left, right = (t, logic_left), (t', logic_right) in
            solve_senior (depth + 1) bound context left right)
      else
        raise (Incomparable_Terms (term_left, term_right))
    | Tuple t, Var s ->
      if Poly.(bound = `Upper) then
        let solve ~key ~data acc =
          let right = key, data in
          solve_senior (depth + 1) bound context left right in
        let rightm = bound_terms_exn bound constrs term_right logic_right in
        Term.Map.fold rightm ~init:context ~f:solve
      else
        let bounds = bound_terms_exn bound constrs term_left logic_left in
        let constrs = set_bound_exn (depth + 1) bound constrs s bounds in
        constrs, logic
    | Var s, Tuple t ->
      if Poly.(bound = `Lower) then
        let solve ~key ~data acc =
          let left = key, data in
          solve_senior (depth + 1) bound context left right in
        let leftm = bound_terms_exn bound constrs term_left logic_left in
        Term.Map.fold leftm ~init:context ~f:solve
      else
        let bounds = bound_terms_exn bound constrs term_right logic_right in
        let constrs = set_bound_exn (depth + 1) bound constrs s bounds in
        constrs, logic
    (* list processing *)
    | List (l, None), Var v ->
      if Poly.(bound = `Upper) then
        let bounds = bound_terms_exn bound constrs term_right logic_right in
        Term.Map.fold bounds ~init:context ~f:(fun ~key ~data acc ->
          solve_senior (depth + 1) bound context left (key, data))
      else
        let bounds = bound_terms_exn bound constrs term_left logic_left in
        let constrs = set_bound_exn (depth + 1) bound constrs v bounds in
        constrs, logic
    | Var v, List (l, None) ->
      if Poly.(bound = `Lower) then
        let bounds = bound_terms_exn bound constrs term_left logic_left in
        Term.Map.fold bounds ~init:context ~f:(fun ~key ~data acc ->
          solve_senior (depth + 1) bound context (key, data) right)
      else
        let bounds = bound_terms_exn bound constrs term_right logic_right in
        let constrs = set_bound_exn (depth + 1) bound constrs v bounds in
        constrs, logic
    | List (t, var), Nil ->
      begin
        let context = List.fold ~init:context ~f:(fun acc el ->
          let left = el, logic_left in
          solve_senior (depth + 1) bound acc left right) t in
        match var with
        | None -> context
        | Some v ->
          solve_senior (depth + 1) bound context (Var v, logic_left) right
      end
    | Nil, List (t, var) ->
      begin
        let context = List.fold ~init:context ~f:(fun acc el ->
          let right = el, logic_right in
          solve_senior (depth + 1) bound acc left right) t in
        match var with
        | None -> context
        | Some v ->
          solve_senior (depth + 1) bound context left (Var v, logic_left)
      end
    | List (t, var), List (t', var') ->
      begin
      (* validate the common head of the list and return remaining elements
         (depending on lists lengths) *)
      let rec validate_head context l1 l2 = match l1, l2 with
      | [], _ -> context, [], l2
      | _, [] -> context, l1, []
      | hd :: tl, hd' :: tl' ->
        let left, right = (hd, logic_left), (hd', logic_right) in
        let context = solve_senior (depth +1) bound context left right in
        validate_head context tl tl' in
      let context, reml, remr = validate_head context t t' in
      (* an error if the tail of the right term is not nil *)
      if Poly.(var = None && remr <> [] &&
          Term.is_nil (List (remr, None)) <> Some true) then
        raise (Term.Incomparable_Terms (term_left, term_right));
      match bound, reml, var, var' with
      | _, [], None, None ->
        if List.is_empty remr then context
        (* the list to the right has higher arity *)
        else raise (Term.Incomparable_Terms (term_left, term_right))
      | `Upper, [], None, Some v' -> context
      | `Upper, [], Some v, _ ->
        let constrs, logic = context in
        let tail_bounds = List.map remr ~f:(fun x ->
          bound_terms_exn bound constrs x logic_right) in
        let tail_list = bound_combinations tail_bounds in
        let context, var_list =
          poly_var_to_list bound context var' logic_right in
        let merged = ref [] in
        if List.is_empty var_list then
          merged := tail_list
        else
          List.iter tail_list ~f:(fun (lst, logic) ->
            List.iter var_list ~f:(fun (lst', logic') ->
              merged := (lst @ lst', Logic.combine logic logic') :: !merged));
        set_list_bound depth bound context v !merged
      | `Upper, reml, _, _ ->
        begin
        let context, var_list =
          poly_var_to_list bound context var' logic_right in
        let heads lst =
          List.fold lst ~init:(Term.Map.empty, [])
            ~f:(fun (hds, tls) (lst, logic) ->
              match lst with
              | hd :: tl ->
                (Term.Map.add hds ~key:hd ~data:logic), (tl, logic) :: tls
              | [] ->
                (Term.Map.add hds ~key:Term.Nil ~data:logic), ([], logic) ::
                    tls) in
        let context, tail_list =
          List.fold reml ~init:(context, var_list)
            ~f:(fun ((constrs, logic), tail_list) x ->
            let head, tail_list = heads tail_list in
            let head = if Term.Map.is_empty head then
              Term.Map.singleton Term.Nil logic_right
            else head in
            let left = Term.Map.singleton term_left logic_left in
            let context =
              solve_senior_multi_exn (depth + 1) bound context left head in
            context, tail_list) in
        match var with
        | Some v -> set_list_bound depth bound context v tail_list
        | None -> context
        end
      | `Lower, _::_, _, None -> context
      | `Lower, [], None, Some v' ->
        let nil = Term.Nil, logic_left in
        let context = List.fold remr ~init:context ~f:(fun context x ->
          solve_senior (depth + 1) bound context nil (x, logic_right)) in
        solve_senior (depth + 1) bound context nil (Var v', logic_right)
      (* lower bounds *)
      | `Lower, (_::_), _, Some v' ->
        let constrs, logic = context in
        let tail_bounds = List.map reml ~f:(fun x ->
          bound_terms_exn bound constrs x logic_left) in
        let tail_list = bound_combinations tail_bounds in
        let context, var_list =
          poly_var_to_list `Upper context var logic_left in
        let merged = ref [] in
        if List.is_empty var_list then
          merged := tail_list
        else
          List.iter tail_list ~f:(fun (lst, logic) ->
            List.iter var_list ~f:(fun (lst', logic') ->
              merged := (lst @ lst', Logic.combine logic logic') :: !merged));
        set_list_bound depth bound context v' !merged
      | `Lower, [], _, _ ->
        begin
        let context, var_list =
          poly_var_to_list `Upper context var logic_left in
        let heads lst =
          List.fold lst ~init:(Term.Map.empty, [])
            ~f:(fun (hds, tls) (lst, logic) ->
              match lst with
              | hd :: tl ->
                (Term.Map.add hds ~key:hd ~data:logic), (tl, logic) :: tls
              | [] ->
                (Term.Map.add hds ~key:Term.Nil ~data:logic), ([], logic) ::
                    tls) in
        let context, tail_list =
          List.fold remr ~init:(context, var_list)
            ~f:(fun ((constrs, logic), tail_list) x ->
            let head, tail_list = heads tail_list in
            let right = Term.Map.singleton term_right logic_right in
            let context =
              solve_senior_multi_exn (depth + 1) bound context head right in
            context, tail_list) in
        match var' with
        | Some v -> set_list_bound depth bound context v tail_list
        | None -> context
        end
      end
    | Switch lm, Var s ->
      let leftm = bound_terms_exn bound constrs term_left logic_left in
      if Poly.(bound = `Upper) then
        let rightm = bound_terms_exn bound constrs term_right logic_right in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else
        let constrs = set_bound_exn (depth + 1) `Lower constrs s leftm in
        constrs, logic
    | Var s, Switch lm ->
      let rightm = bound_terms_exn bound constrs term_right logic_right in
      if Poly.(bound = `Lower) then
        let leftm = bound_terms_exn bound constrs term_left logic_left in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else 
        let constrs = set_bound_exn (depth + 1) `Upper constrs s rightm in
        constrs, logic
    | Switch lm, Switch lm' ->
      let left_map = Term.logic_map_to_term_map lm in
      let right_map = Term.logic_map_to_term_map lm' in
      solve_senior_multi_exn (depth + 1) bound context left_map right_map
    | t, Switch lm ->
      let left_map = Term.Map.singleton term_left logic_left in
      let right_map = Term.logic_map_to_term_map lm in
      solve_senior_multi_exn (depth + 1) bound context left_map right_map
    | Switch lm, t ->
      let right_map = Term.Map.singleton term_right logic_right in
      let left_map = Term.logic_map_to_term_map lm in
      solve_senior_multi_exn (depth + 1) bound context left_map right_map
    | t, t' ->
      if Int.(Term.seniority_exn t t' = -1) then
        raise (Term.Incomparable_Terms (t, t'))
      else
        context
  with Term.Incomparable_Terms (t1, t2) ->
    let logic = Logic.combine logic_left logic_right in
    if Logic.(logic = True) then
      error t1 t2
    else
      let constrs, bool_constrs = context in
      constrs, Logic.Set.add bool_constrs (Logic.Not logic)

and solve_senior_multi_exn depth bound context leftm rightm =
  Term.Map.fold leftm ~init:context ~f:(fun ~key ~data acc ->
    let term_left, logic_left = key, data in
    Term.Map.fold rightm ~init:acc ~f:(fun ~key ~data acc ->
      let term_right, logic_right = key, data in
      solve_senior depth bound acc (term_left, logic_left)
        (term_right, logic_right)))

let resolve_bound_constraints topo loops =
  let ctx = ref (String.Map.empty, Logic.Set.empty) in
  let apply bound (left, right) =
    List.iter ~f:(fun t ->
      let t_map = Term.Map.singleton t Logic.True in
      List.iter ~f:(fun t' ->
        let t_map' = Term.Map.singleton t' Logic.True in
        ctx := solve_senior_multi_exn 0 bound !ctx t_map t_map'
        ) right
      ) left in
  let topo' = List.rev topo in
  Log.infof "setting least upper bounds for constraints";
  List.iter ~f:(apply `Upper) topo';
  Log.infof "setting greatest lower bounds for constraints";
  List.iter ~f:(apply `Lower) topo;
  List.iter ~f:(apply `Upper) (List.rev loops);
  List.iter ~f:(apply `Lower) loops;
  !ctx

let bounds_to_bool constrs =
  let bools = ref Logic.Set.empty in
  let add ~key ~data =
    let lb_map, ub_map = data in
    let clause = ref [] in
    Term.Map.iter lb_map ~f:(fun ~key ~data ->
      let left_term, left_logic = key, data in
      Term.Map.iter ub_map ~f:(fun ~key ~data ->
        let right_term, right_logic = key, data in
        try
          let comp = Term.seniority_exn left_term right_term in
          if comp > -1 then
            clause := (Logic.combine left_logic right_logic) :: !clause
          else
            bools := Logic.Set.add !bools
              (Logic.Not (Logic.combine left_logic right_logic))
         with Term.Incomparable_Terms _ ->
          bools := Logic.Set.add !bools
            (Logic.Not (Logic.combine left_logic right_logic))));
    if not (List.is_empty !clause) then
      bools := Logic.Set.add !bools (Logic.Or !clause) in
  String.Map.iter constrs ~f:add;
  !bools

let unify_exn g =
  Log.debugf "creating a traversal order for constraints";
  let topo, loops = Network.traversal_order g in
  let constrs, logic = resolve_bound_constraints topo loops in
  constrs, Logic.Set.union logic (bounds_to_bool constrs)
