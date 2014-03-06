open Core.Std

exception Unsatisfiability_Error of string

let unsat_error msg =
  let open Errors in
  raise (Unsatisfiability_Error (error msg))

let print_map tm =
  let tl = Logic.Map.to_alist tm in
  let sl = List.map tl ~f:(fun (l, t) ->
    Printf.sprintf "[%s]%s" (Logic.to_string l) (Term.to_string t)) in
  String.concat ~sep:", " sl

let get_bound_exn bound constrs var =
  let lower, upper = String.Map.find_exn constrs var in
  if bound = `Lower && Logic.Map.is_empty lower then
    failwith ("lack of lower bound for variable $" ^ var)
  else if bound = `Upper && Logic.Map.is_empty upper then
    Logic.Map.singleton Logic.True Term.Nil
  else if bound = `Upper then upper
  else lower

let merge_bounds depth bound old_terms new_terms =
  let map = ref Logic.Map.empty in
  let iter ~key ~data =
    let logic, term = key, data in
    let iter' ~key ~data =
      let logic', term' = key, data in
      try
        let relation = Term.seniority_exn term term' in
        let combined = Logic.combine logic logic' in
        if (bound = `Upper && relation < 1) ||
          (bound = `Lower && relation > -1) then
          map := Logic.Map.add !map combined term'
        else
          map := Logic.Map.add !map combined term
      with Term.Incomparable_Terms _ -> () in
    Logic.Map.iter new_terms ~f:iter' in
  if Logic.Map.is_empty old_terms && Logic.Map.is_empty new_terms then
    if bound = `Upper then Logic.Map.singleton Logic.True Term.Nil
    else Logic.Map.empty
  else if Logic.Map.is_empty old_terms then new_terms
  else if Logic.Map.is_empty new_terms then old_terms
  else begin
    Logic.Map.iter old_terms ~f:iter;
    let s = if bound = `Upper then "upper" else "lower" in
    Log.debugf "%smerged %s bounds {%s} and {%s} into {%s}"
      (String.make depth ' ') s (print_map old_terms) (print_map new_terms)
        (print_map !map);
    !map
  end

let combine_bounds bound old_terms new_terms =
  Logic.Map.fold new_terms ~init:old_terms ~f:(fun ~key ~data acc ->
    let new_term = data in
    Logic.Map.change acc key (function
    | None -> Some data
    | Some old_term ->
      try
        let relation = Term.seniority_exn old_term new_term in
        if (bound = `Upper && relation < 1) ||
          (bound = `Lower && relation > -1) then Some new_term
        else Some old_term
      with Term.Incomparable_Terms (t1, t2) ->
        unsat_error (Printf.sprintf "constraint violation between old bound
         (%s) and new one (%s)" (Term.to_string old_term)
         (Term.to_string new_term))))

let rec bound_combinations_list = function
  | [] -> []
  | hd :: [] ->
    Logic.Map.fold hd ~init:[]
      ~f:(fun ~key ~data acc -> (key, [data]) :: acc)
  | hd :: tl ->
    let tail_bounds = bound_combinations_list tl in
    Logic.Map.fold hd ~init:[]
      ~f:(fun ~key ~data acc ->
        let logic, term = key, data in
        List.fold tail_bounds ~init:acc
          ~f:(fun acc (logic', lst) ->
          (Logic.combine logic logic', term :: lst) :: acc))

let rec bound_combinations_alist = function
  | [] -> []
  | (s, (l, map)) :: [] ->
    Logic.Map.fold map ~init:[]
      ~f:(fun ~key ~data acc -> (key, [s, (l, data)]) :: acc)
  | (s, (l, map)) :: tl ->
    let tail_bounds = bound_combinations_alist tl in
    Logic.Map.fold map ~init:[]
      ~f:(fun ~key ~data acc ->
        let logic, term = key, data in
        List.fold tail_bounds ~init:acc
          ~f:(fun acc (logic', lst) ->
          (Logic.combine logic logic', (s, (l, term)) :: lst) :: acc))

let rec merge_maps typ bound left right logic =
  let result = ref [logic, String.Map.empty] in
  String.Map.iter2 left right ~f:(fun ~key ~data ->
    let add l t =
      List.map !result ~f:(fun (logic, map) ->
        Logic.combine l logic, String.Map.add map ~key ~data:(l, t)) in
      match data with
      | `Left (l, t)
      | `Right (l, t) ->
        result := add l t
      | `Both ((l, t), (l', t')) ->
        (* TODO: logic expressions must be not equal, but produce the same
                 model. A solver must be executed here *)
        if l = l' then
          let typ_str = if typ = `Record then "records" else "choices" in
          if (bound = `Upper && typ = `Record) ||
            (bound = `Lower && typ = `Choice) then
            unsat_error ("unresolvable bound constraints for " ^ typ_str)
          else 
            (* TODO tighten bounds of the tail variable *)
            ()
        else result := (add l t) @ (add l' t'));
    !result

let rec bound_terms_exn bound constrs logic term =
  let open Term in
  match term with
  | Nil | Int _ | Symbol _ -> Logic.Map.singleton logic term
  | Switch x ->
    Logic.Map.fold x ~init:Logic.Map.empty
      ~f:(fun ~key ~data acc ->
        let logic' = key in
        let bounds = bound_terms_exn bound constrs logic data in
        let bounds = Logic.Map.fold bounds ~init:Logic.Map.empty
          ~f:(fun ~key ~data acc -> Logic.Map.add acc ~data
            ~key:(Logic.combine logic (Logic.combine key logic'))) in
        combine_bounds bound acc bounds)
  | Tuple x ->
    let l = List.map x ~f:(fun x -> bound_terms_exn bound constrs logic x) in
    let term_list =
      List.map (bound_combinations_list l) ~f:(fun (l, t) -> l, Tuple t) in
    let result = Logic.Map.of_alist_exn term_list in
    result
  | List (x, s) ->
    let l = List.map x ~f:(fun x -> bound_terms_exn bound constrs logic x) in
    let term_list = bound_combinations_list l in
    begin
      match s with
      | None ->
        Logic.Map.of_alist_exn
          (List.map term_list ~f:(fun (l, t) -> l, List (t, None)))
      | Some var ->
        let bounds = bound_terms_exn bound constrs logic (Var var) in
        let lst = List.fold term_list ~init:[] ~f:(fun acc (logic', head) ->
          Logic.Map.fold bounds ~init:acc ~f:(fun ~key ~data acc ->
            match data with
            | Term.List (l, None) ->
              (Logic.combine logic (Logic.combine key logic'), head @ l) :: acc
            | Term.List (l, _) ->
              raise (Unsatisfiability_Error
                (Printf.sprintf "expected a ground list term, but %s found"
                  (Term.to_string data)))
            | _ -> acc)) in
        Logic.Map.of_alist_exn
          (List.map  lst ~f:(fun (l, t) -> l, List (t, None)))
    end
  | Record (map, s) ->
    let b = String.Map.map map
      ~f:(fun (l, t) -> l, bound_terms_exn bound constrs logic t) in
    let term_map = bound_combinations_alist (String.Map.to_alist b) in
    begin
      match s with
      | None ->
        let combined = List.map term_map
          ~f:(fun (logic, lst) ->
          logic, Record (String.Map.of_alist_exn lst, None)) in
        Logic.Map.of_alist_exn combined
      | Some var ->
        let bounds = bound_terms_exn `Upper constrs logic (Var var) in
        let data = List.map term_map ~f:(fun (logic, lst) ->
          logic, String.Map.of_alist_exn lst) in
        let combined = List.fold data ~init:[] ~f:(fun acc (logic', head) ->
          Logic.Map.fold bounds ~init:acc ~f:(fun ~key ~data acc ->
          match data with
          | Term.Record (map, None) ->
            let lst = merge_maps `Record bound head map logic' in
            lst @ acc
          | Term.Nil ->
            let lst = merge_maps `Record bound head String.Map.empty logic' in
            lst @ acc
          | Term.Record (map, _) ->
              raise (Unsatisfiability_Error
                (Printf.sprintf "expected a ground list term, but %s found"
                  (Term.to_string data)))
          | _ -> acc)) in
        (* if tail variable does not have bounding term that is a record,
           throw error *)
        let _ = if List.is_empty combined then
          let b = if Poly.(bound = `Upper) then "upper" else "lower" in
          raise (Unsatisfiability_Error
            (Printf.sprintf "Missing record as a %s bound for variable $%s"
            b var)) in
        (* vefify the consistency of generated bounds *)
        let l = List.map combined
          ~f:(fun (logic, lst) -> logic, Record (lst, None)) in
        Logic.Map.of_alist_exn l
    end
  (* TODO fix copy/paste *)
  | Choice (map, s) ->
    let b = String.Map.map map
      ~f:(fun (l, t) -> l, bound_terms_exn bound constrs logic t) in
    let term_map = bound_combinations_alist (String.Map.to_alist b) in
    begin
      match s with
      | None ->
        let combined = List.map term_map
          ~f:(fun (logic, lst) ->
          logic, Choice (String.Map.of_alist_exn lst, None)) in
        Logic.Map.of_alist_exn combined
      | Some var ->
        let bounds = bound_terms_exn `Upper constrs logic (Var var) in
        let data = List.map term_map ~f:(fun (logic, lst) ->
          logic, String.Map.of_alist_exn lst) in
        let combined = List.fold data ~init:[] ~f:(fun acc (logic', head) ->
          Logic.Map.fold bounds ~init:acc ~f:(fun ~key ~data acc ->
          match data with
          | Term.Choice (map, None) ->
            let lst = merge_maps `Choice bound head map logic' in
            lst @ acc
          | Term.Nil ->
            let lst = merge_maps `Choice bound head String.Map.empty logic' in
            lst @ acc
          | Term.Choice (map, _) ->
              raise (Unsatisfiability_Error
                (Printf.sprintf "expected a ground list term, but %s found"
                  (Term.to_string data)))
          | _ -> acc)) in
        (* if tail variable does not have bounding term that is a choice,
           throw error *)
        let _ = if List.is_empty combined then
          let b = if Poly.(bound = `Upper) then "upper" else "lower" in
          raise (Unsatisfiability_Error
            (Printf.sprintf "Missing record as a %s bound for variable $%s"
            b var)) in
        (* vefify the consistency of generated bounds *)
        let l = List.map combined
          ~f:(fun (logic, lst) -> logic, Choice (lst, None)) in
        Logic.Map.of_alist_exn l
    end
  | Var x -> get_bound_exn bound constrs x

let set_bound_exn depth bound constrs var terms =
  let simplify t =
    let t = Term.canonize t in
    if Term.is_nil_exn t then Term.Nil else t in
  let terms = Logic.Map.fold ~init:Logic.Map.empty
    ~f:(fun ~key ~data acc -> Logic.Map.add ~key ~data:(simplify data) acc)
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
        Some (Logic.Map.empty, terms)
      else Some (terms, Logic.Map.empty)
    | Some (l, u) ->
      if bound = `Upper then
        let merged = merge_bounds (depth + 1) bound u terms in
        if Logic.Map.is_empty merged then
          raise (unsat_error
            (Printf.sprintf "upper bounds for variable $%s are inconsistent" 
              var))
        else
          Log.debugf "%s%s for variable $%s to {%s}" (String.make depth ' ') b
            var (print_map merged);
          Some (l, merged)
      else
        let merged = merge_bounds (depth + 1) bound l terms in
        if Logic.Map.is_empty merged then
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
    let bounds = bound_terms_exn bound constrs logic_constr (Term.Var v) in
    Logic.Map.fold bounds ~init:(context, [])
      ~f:(fun ~key ~data (context, acc) ->
        match data with
        | Term.List (x, None) -> context, (key, x) :: acc
        | Term.List (_, _) -> failwith "expected ground term"
        | Term.Nil -> context, acc
        | _ ->
          let constrs, logic = context in
          let b = Logic.Not (Logic.combine key logic_constr) in
          (constrs, Logic.Set.add logic b), acc)

let set_list_constraints context map =
  Logic.Map.fold map ~init:context ~f:(fun ~key ~data (constrs, logic) ->
    match data with
    | Term.List _
    | Term.Nil -> constrs, logic
    | _ -> constrs, Logic.Set.add logic (Logic.Not key))

let set_list_bound depth bound (c, l) v lst =
  let map = List.fold lst ~init:Logic.Map.empty ~f:(fun acc (logic, lst) ->
    Logic.Map.add acc ~key:logic ~data:(Term.List (lst, None))) in
  let c = set_bound_exn (depth + 1) bound c v map in
  c, l

let rec solve_senior depth bound context left right =
  let constrs, logic = context in
  let logic_left, term_left = left in
  let term_left, l = Equations.union term_left in
  let logic_left = Logic.combine l logic_left in
  let logic_right, term_right = right in
  let term_right, l = Equations.union term_right in
  let logic_right = Logic.combine l logic_right in
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
        let rightm = bound_terms_exn bound constrs logic_right term_right in
        let constrs = set_bound_exn (depth + 1) `Upper constrs s rightm in
        constrs, logic
      else
        let leftm = bound_terms_exn `Upper constrs logic_left term_left in
        let constrs = set_bound_exn (depth + 1) `Lower constrs s' leftm in
        constrs, logic
    (* atomic terms *)
    | (Nil | Int _ | Symbol _), Var s ->
      let leftm = bound_terms_exn `Upper constrs logic_left term_left in
      if Poly.(bound = `Upper) then
        let rightm = bound_terms_exn bound constrs logic_right term_right in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else
        let constrs = set_bound_exn (depth + 1) bound constrs s leftm in
        constrs, logic
    | Var s, (Nil | Int _ | Symbol _) ->
      let rightm = bound_terms_exn bound constrs logic_right term_right in
      if Poly.(bound = `Lower) then
        let leftm = bound_terms_exn `Upper constrs logic_left term_left in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else 
        let constrs = set_bound_exn (depth + 1) `Upper constrs s rightm in
        constrs, logic
    (* tuple processing *)
    | Tuple t, Nil ->
        List.fold ~init:context ~f:(fun acc el ->
          let left = logic_left, el in
          solve_senior (depth + 1) bound acc left right) t
    | Nil, Tuple t ->
        List.fold ~init:context ~f:(fun acc el ->
          let right = logic_right, el in
          solve_senior (depth + 1) bound acc left right) t
    | Tuple t, Tuple t' when Int.(List.length t = List.length t') ->
      if Int.(List.length t = List.length t') then
        List.fold2_exn t t' ~init:context
          ~f:(fun context t t' ->
            let left, right = (logic_left, t), (logic_right, t') in
            solve_senior (depth + 1) bound context left right)
      else
        raise (Incomparable_Terms (term_left, term_right))
    | Tuple t, Var s ->
      if Poly.(bound = `Upper) then
        let solve ~key ~data acc =
          let right = key, data in
          solve_senior (depth + 1) bound context left right in
        let rightm = bound_terms_exn bound constrs logic_right term_right in
        Logic.Map.fold rightm ~init:context ~f:solve
      else
        let bounds = bound_terms_exn `Upper constrs logic_left term_left in
        let constrs = set_bound_exn (depth + 1) bound constrs s bounds in
        constrs, logic
    | Var s, Tuple t ->
      if Poly.(bound = `Lower) then
        let solve ~key ~data acc =
          let left = key, data in
          solve_senior (depth + 1) bound context left right in
        let leftm = bound_terms_exn `Upper constrs logic_left term_left in
        Logic.Map.fold leftm ~init:context ~f:solve
      else
        let bounds = bound_terms_exn bound constrs logic_right term_right in
        let constrs = set_bound_exn (depth + 1) bound constrs s bounds in
        constrs, logic
    (* list processing *)
    | List _, Var v ->
      if Poly.(bound = `Upper) then
        let bounds = bound_terms_exn bound constrs logic_right term_right in
        Logic.Map.fold bounds ~init:context ~f:(fun ~key ~data acc ->
          solve_senior (depth + 1) bound context left (key, data))
      else
        let bounds = bound_terms_exn `Lower constrs logic_left term_left in
        let constrs = set_bound_exn (depth + 1) bound constrs v bounds in
        constrs, logic
    | Var v, List _ ->
      if Poly.(bound = `Lower) then
        let bounds = bound_terms_exn `Upper constrs logic_left term_left in
        Logic.Map.fold bounds ~init:context ~f:(fun ~key ~data acc ->
          solve_senior (depth + 1) bound context (key, data) right)
      else
        let bounds = bound_terms_exn bound constrs logic_right term_right in
        let constrs = set_bound_exn (depth + 1) bound constrs v bounds in
        constrs, logic
    | List (t, var), Nil ->
      begin
        let context = List.fold ~init:context ~f:(fun acc el ->
          let left = logic_left, el in
          solve_senior (depth + 1) bound acc left right) t in
        match var with
        | None -> context
        | Some v ->
          solve_senior (depth + 1) bound context (logic_left, Var v) right
      end
    | Nil, List (t, var) ->
      begin
        let context = List.fold ~init:context ~f:(fun acc el ->
          let right = logic_right, el in
          solve_senior (depth + 1) bound acc left right) t in
        match var with
        | None -> context
        | Some v ->
          solve_senior (depth + 1) bound context left (logic_left, Var v)
      end
    | List (t, var), List (t', var') ->
      begin
      (* validate the common head of the list and return remaining elements
         (depending on lists lengths) *)
      let rec validate_head context l1 l2 = match l1, l2 with
      | [], _ -> context, [], l2
      | _, [] -> context, l1, []
      | hd :: tl, hd' :: tl' ->
        let left, right = (logic_left, hd), (logic_right, hd') in
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
          bound_terms_exn bound constrs logic_right x) in
        let tail_list = bound_combinations_list tail_bounds in
        let context, var_list =
          poly_var_to_list bound context var' logic_right in
        let merged = ref [] in
        if List.is_empty var_list then
          merged := tail_list
        else
          List.iter tail_list ~f:(fun (logic, lst) ->
            List.iter var_list ~f:(fun (logic', lst') ->
              merged := (Logic.combine logic logic', lst @ lst') :: !merged));
        set_list_bound depth bound context v !merged
      | `Upper, reml, _, _ ->
        begin
        let context, var_list =
          poly_var_to_list bound context var' logic_right in
        let heads lst =
          List.fold lst ~init:(Logic.Map.empty, [])
            ~f:(fun (hds, tls) (logic, lst) ->
              match lst with
              | hd :: tl ->
                (Logic.Map.add hds ~key:logic ~data:hd), (logic, tl) :: tls
              | [] ->
                (Logic.Map.add hds ~key:logic ~data:Term.Nil), (logic, []) ::
                    tls) in
        let context, tail_list =
          List.fold reml ~init:(context, var_list)
            ~f:(fun ((constrs, logic), tail_list) x ->
            let head, tail_list = heads tail_list in
            let head = if Logic.Map.is_empty head then
              Logic.Map.singleton logic_right Term.Nil
            else head in
            let left = Logic.Map.singleton logic_left term_left in
            let context =
              solve_senior_multi_exn (depth + 1) bound context left head in
            context, tail_list) in
        match var with
        | Some v -> set_list_bound depth bound context v tail_list
        | None -> context
        end
      | `Lower, _::_, _, None -> context
      | `Lower, [], None, Some v' ->
        let nil = logic_left, Term.Nil in
        let context = List.fold remr ~init:context ~f:(fun context x ->
          solve_senior (depth + 1) bound context nil (logic_right, x)) in
        solve_senior (depth + 1) bound context nil (logic_right, Var v')
      (* lower bounds *)
      | `Lower, (_::_), _, Some v' ->
        let constrs, logic = context in
        (* set constraints on type of term for polymorphic variable *)
        let context =
          match var with
          | None -> context
          | Some v ->
            let b = bound_terms_exn `Lower constrs logic_left (Var v) in
            set_list_constraints context b in
        let tail_bounds = List.map reml ~f:(fun x ->
          bound_terms_exn `Upper constrs logic_left x) in
        let tail_list = bound_combinations_list tail_bounds in
        let context, var_list =
          poly_var_to_list `Upper context var logic_left in
        let merged = ref [] in
        if List.is_empty var_list then
          merged := tail_list
        else
          List.iter tail_list ~f:(fun (logic, lst) ->
            List.iter var_list ~f:(fun (logic', lst') ->
              merged := (Logic.combine logic logic', lst @ lst') :: !merged));
        set_list_bound depth bound context v' !merged
      | `Lower, [], _, _ ->
        begin
        (* set constraints on type of term for polymorphic variable *)
        let context =
          match var with
          | None -> context
          | Some v ->
            let b = bound_terms_exn `Lower constrs logic_left (Var v) in
            set_list_constraints context b in
        let context, var_list =
          poly_var_to_list `Upper context var logic_left in
        let heads lst =
          List.fold lst ~init:(Logic.Map.empty, [])
            ~f:(fun (hds, tls) (logic, lst) ->
              match lst with
              | hd :: tl ->
                (Logic.Map.add hds ~key:logic ~data:hd), (logic, tl) :: tls
              | [] ->
                (Logic.Map.add hds ~key:logic ~data:Term.Nil), (logic, []) ::
                    tls) in
        let context, tail_list =
          List.fold remr ~init:(context, var_list)
            ~f:(fun ((constrs, logic), tail_list) x ->
            let head, tail_list = heads tail_list in
            let right = Logic.Map.singleton logic_right term_right in
            let context =
              solve_senior_multi_exn (depth + 1) bound context head right in
            context, tail_list) in
        match var' with
        | Some v -> set_list_bound depth bound context v tail_list
        | None -> context
        end
      end
    (* record/choice processing *)
    | Choice _, Var s
    | Record _, Var s ->
      if Poly.(bound = `Upper) then
        let bounds = bound_terms_exn bound constrs logic_right term_right in
        Logic.Map.fold bounds ~init:context ~f:(fun ~key ~data acc ->
          solve_senior (depth + 1) bound context left (key, data))
      else
        let bounds = bound_terms_exn `Lower constrs logic_left term_left in
        let constrs = set_bound_exn (depth + 1) bound constrs s bounds in
        constrs, logic
    | Var s, Choice _
    | Var s, Record _ ->
      if Poly.(bound = `Lower) then
        let bounds = bound_terms_exn `Upper constrs logic_left term_left in
        Logic.Map.fold bounds ~init:context ~f:(fun ~key ~data acc ->
          solve_senior (depth + 1) bound context (key, data) right)
      else
        let bounds = bound_terms_exn bound constrs logic_right term_right in
        let constrs = set_bound_exn (depth + 1) bound constrs s bounds in
        constrs, logic
    | Choice (map, var), Nil
    | Record (map, var), Nil ->
      begin
        let context = String.Map.fold map ~init:context
          ~f:(fun ~key ~data acc ->
          let l, t = data in
          solve_senior (depth + 1) bound acc (l, t) right) in
        match var with
        | None -> context
        | Some v ->
          solve_senior (depth + 1) bound context (logic_left, Var v) right
      end
    | Nil, Choice (map, var)
    | Nil, Record (map, var) ->
      begin
        let context = String.Map.fold map ~init:context
          ~f:(fun ~key ~data acc ->
          let l, t = data in
          solve_senior (depth + 1) bound acc left (l, t)) in
        match var with
        | None -> context
        | Some v ->
          solve_senior (depth + 1) bound context left (logic_left, Var v)
      end
    | Record (r, v), Record (r', v') ->
      begin
        if Poly.(bound = `Upper) then
          let bounds = bound_terms_exn bound constrs logic_right term_right in
          (* set bounds for all terms from the left to nil *)
          let context = String.Map.fold r ~init:context
            ~f:(fun ~key ~data acc ->
              let (guard, term) = data in solve_senior (depth + 1) bound acc
                (Logic.combine guard logic_left, term)
                (logic_right, Nil)) in
          let ctx = ref context in
          let var_bounds = ref Logic.Map.empty in
          Logic.Map.iter bounds ~f:(fun ~key ~data ->
            let logic = Logic.combine key logic_right in
            match data with
            | Record (r', None) ->
              begin
              let var_rec = ref String.Map.empty in
              let var_logic = ref logic in
              String.Map.iter r' ~f:(fun ~key ~data ->
                let label, (guard, term) = key, data in
                match String.Map.find r key with
                | None -> var_rec := String.Map.add !var_rec ~key:label
                  ~data:(Logic.combine guard logic, term);
                  var_logic := Logic.combine !var_logic guard
                | Some (guard', term') ->
                  try
                    let constrs, logic = solve_senior (depth + 1) bound !ctx (guard', term') (guard, term) in
                    let logic = Logic.Set.add logic (Logic.Or [Logic.Not guard; guard']) in
                    ctx := constrs, logic
                  with Unsatisfiability_Error _ ->
                    var_logic := Logic.combine !var_logic
                      (Logic.combine (Logic.Not guard) (Logic.Not guard')));
                if not (String.Map.is_empty !var_rec) then
                  var_bounds := Logic.Map.add !var_bounds ~key:!var_logic ~data:(Record(!var_rec, None))
              end 
            | _ -> failwith "invalid term");
            let constrs, logic = !ctx in
            match v with
            | None ->
              constrs, Logic.Map.fold ~init:logic ~f:(fun ~key ~data acc ->
                Logic.Set.add acc (Logic.Not key)) !var_bounds
            | Some var ->
              let var_bounds =
                if Logic.Map.is_empty !var_bounds then
                  ref (Logic.Map.singleton logic_left Term.Nil)
                else var_bounds in
              let constrs = set_bound_exn (depth + 1) bound constrs var !var_bounds in
              constrs, logic
        else
          let bounds = bound_terms_exn bound constrs logic_left term_left in
          (* set bounds for all terms from the left to nil *)
(*
          let context = String.Map.fold r' ~init:context
            ~f:(fun ~key ~data acc ->
              let (guard, term) = data in solve_senior (depth + 1) bound acc
                (term, Logic.combine guard logic_left)
                (Nil, logic_right)) in
*)
          let ctx = ref context in
          let var_bounds = ref Logic.Map.empty in
          Logic.Map.iter bounds ~f:(fun ~key ~data ->
            let logic = Logic.combine key logic_left in
            match data with
            | Record (r, None) ->
              begin
              let var_rec = ref String.Map.empty in
              let var_logic = ref logic in
              String.Map.iter r ~f:(fun ~key ~data ->
                let label, (guard, term) = key, data in
                match String.Map.find r' label with
                | None ->
                  var_rec := String.Map.add !var_rec ~key:label
                  ~data:(Logic.combine guard logic, term);
                  var_logic := Logic.combine !var_logic guard
                | Some (guard', term') ->
                  try
                    let constrs, logic = solve_senior (depth + 1) bound !ctx (guard, term) (guard', term') in
                    let logic = Logic.Set.add logic (Logic.Or [Logic.Not guard; guard']) in
                    ctx := constrs, logic
                  with Unsatisfiability_Error _ ->
                    var_logic := Logic.combine !var_logic
                      (Logic.combine (Logic.Not guard) (Logic.Not guard')));
                if not (String.Map.is_empty !var_rec) then
                  var_bounds := Logic.Map.add !var_bounds ~key:!var_logic ~data:(Record(!var_rec, None))
              end 
            | _ -> failwith "invalid term");
            let constrs, logic = !ctx in
            match v' with
            | None ->
              constrs, logic
            | Some var ->
              let constrs = set_bound_exn (depth + 1) bound constrs var !var_bounds in
              constrs, logic
      end
    | Choice (r, v), Choice (r', v') ->
      begin
        if Poly.(bound = `Lower) then
          let bounds = bound_terms_exn bound constrs logic_left term_left in
          (* set bounds for all terms from the left to nil *)
(*
          let context = String.Map.fold r ~init:context
            ~f:(fun ~key ~data acc ->
              let (guard, term) = data in solve_senior (depth + 1) bound acc
                (Logic.combine guard logic_left, term)
                (logic_right, Nil)) in
*)
          let ctx = ref context in
          let var_bounds = ref Logic.Map.empty in
          Logic.Map.iter bounds ~f:(fun ~key ~data ->
            let logic = Logic.combine key logic_left in
            match data with
            | Choice (r, None) ->
              begin
              let var_rec = ref String.Map.empty in
              let var_logic = ref logic in
              String.Map.iter r ~f:(fun ~key ~data ->
                let label, (guard, term) = key, data in
                match String.Map.find r' key with
                | None -> var_rec := String.Map.add !var_rec ~key:label
                  ~data:(Logic.combine guard logic, term);
                  var_logic := Logic.combine !var_logic guard
                | Some (guard', term') ->
                  try
                    let constrs, logic = solve_senior (depth + 1) bound !ctx (guard, term) (guard', term') in
                    let logic = Logic.Set.add logic (Logic.Or [Logic.Not guard; guard']) in
                    ctx := constrs, logic
                  with Unsatisfiability_Error _ ->
                    var_logic := Logic.combine !var_logic
                      (Logic.combine (Logic.Not guard) (Logic.Not guard')));
                if not (String.Map.is_empty !var_rec) then
                  var_bounds := Logic.Map.add !var_bounds ~key:!var_logic ~data:(Choice(!var_rec, None))
              end 
            | _ -> failwith "invalid term");
            let constrs, logic = !ctx in
            match v' with
            | None ->
              constrs, Logic.Map.fold ~init:logic ~f:(fun ~key ~data acc ->
                Logic.Set.add acc (Logic.Not key)) !var_bounds
            | Some var ->
              let var_bounds =
                if Logic.Map.is_empty !var_bounds then
                  ref (Logic.Map.singleton logic_right Term.Nil)
                else var_bounds in
              let constrs = set_bound_exn (depth + 1) bound constrs var !var_bounds in
              constrs, logic
        else
          let bounds = bound_terms_exn bound constrs logic_right term_right in
          (* set bounds for all terms from the left to nil *)
(*
          let context = String.Map.fold r' ~init:context
            ~f:(fun ~key ~data acc ->
              let (guard, term) = data in solve_senior (depth + 1) bound acc
                (term, Logic.combine guard logic_left)
                (Nil, logic_right)) in
*)
          let ctx = ref context in
          let var_bounds = ref Logic.Map.empty in
          Logic.Map.iter bounds ~f:(fun ~key ~data ->
            let logic = Logic.combine key logic_right in
            match data with
            | Choice (r', None) ->
              begin
              let var_rec = ref String.Map.empty in
              let var_logic = ref logic in
              String.Map.iter r' ~f:(fun ~key ~data ->
                let label, (guard, term) = key, data in
                match String.Map.find r label with
                | None ->
                  var_rec := String.Map.add !var_rec ~key:label
                  ~data:(Logic.combine guard logic, term);
                  var_logic := Logic.combine !var_logic guard
                | Some (guard', term') ->
                  try
                    let constrs, logic = solve_senior (depth + 1) bound !ctx (guard', term') (guard, term) in
                    let logic = Logic.Set.add logic (Logic.Or [Logic.Not guard; guard']) in
                    ctx := constrs, logic
                  with Unsatisfiability_Error _ ->
                    var_logic := Logic.combine !var_logic
                      (Logic.combine (Logic.Not guard) (Logic.Not guard')));
                if not (String.Map.is_empty !var_rec) then
                  var_bounds := Logic.Map.add !var_bounds ~key:!var_logic ~data:(Choice(!var_rec, None))
              end 
            | _ -> failwith "invalid term");
            let constrs, logic = !ctx in
            match v with
            | None ->
              constrs, logic
            | Some var ->
              let constrs = set_bound_exn (depth + 1) bound constrs var !var_bounds in
              constrs, logic
      end

    (* switch processing *)
    | Switch leftm, Var s ->
      if Poly.(bound = `Upper) then
        let rightm = bound_terms_exn bound constrs logic_right term_right in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else
        let leftm = bound_terms_exn `Upper constrs logic_left term_left in
        let constrs = set_bound_exn (depth + 1) `Lower constrs s leftm in
        constrs, logic
    | Var s, Switch rightm ->
      if Poly.(bound = `Lower) then
        let leftm = bound_terms_exn `Upper constrs logic_left term_left in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else 
        let rightm = bound_terms_exn bound constrs logic_right term_right in
        let constrs = set_bound_exn (depth + 1) `Upper constrs s rightm in
        constrs, logic
    | Switch leftm, Switch rightm ->
      solve_senior_multi_exn (depth + 1) bound context leftm rightm
    | t, Switch right_map ->
      let left_map = Logic.Map.singleton logic_left term_left in
      solve_senior_multi_exn (depth + 1) bound context left_map right_map
    | Switch left_map, t ->
      let right_map = Logic.Map.singleton logic_right term_right in
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
  Logic.Map.fold leftm ~init:context ~f:(fun ~key ~data acc ->
    let logic_left, term_left = key, data in
    Logic.Map.fold rightm ~init:acc ~f:(fun ~key ~data acc ->
      let logic_right, term_right = key, data in
      solve_senior depth bound acc (logic_left, term_left)
        (logic_right, term_right)))

let resolve_bound_constraints topo loops =
  let ctx = ref (String.Map.empty, Logic.Set.empty) in
  let apply bound (left, right) =
    List.iter ~f:(fun t ->
      let l_map = Logic.Map.singleton Logic.True t in
      List.iter ~f:(fun t' ->
        let l_map' = Logic.Map.singleton Logic.True t' in
        ctx := solve_senior_multi_exn 0 bound !ctx l_map l_map'
        ) right
      ) left in
  let topo' = List.rev topo in
  Log.infof "setting least upper bounds for constraints";
  List.iter ~f:(apply `Upper) topo';
  Log.infof "setting greatest lower bounds for constraints";
  List.iter ~f:(apply `Lower) topo;
  List.iter ~f:(apply `Upper) (List.rev loops);
  List.iter ~f:(apply `Lower) loops;
  Log.infof "finished resolving bound constraints";
  !ctx

let bounds_to_bool constrs =
  let bools = ref Logic.Set.empty in
  let add ~key ~data =
    let lb_map, ub_map = data in
    let clause = ref [] in
    Logic.Map.iter lb_map ~f:(fun ~key ~data ->
      let left_logic, left_term = key, data in
      Logic.Map.iter ub_map ~f:(fun ~key ~data ->
        let right_logic, right_term = key, data in
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
