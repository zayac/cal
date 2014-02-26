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

let rec bound_combinations_list = function
  | [] -> []
  | hd :: [] ->
    Term.Map.fold hd ~init:[]
      ~f:(fun ~key ~data acc -> ([key], data) :: acc)
  | hd :: tl ->
    let tail_bounds = bound_combinations_list tl in
    Term.Map.fold hd ~init:[]
      ~f:(fun ~key ~data acc ->
        let term, logic = key, data in
        List.fold tail_bounds ~init:acc
          ~f:(fun acc (lst, logic') ->
          (term :: lst, Logic.combine logic logic') :: acc))

let rec bound_combinations_alist = function
  | [] -> []
  | (s, (l, map)) :: [] ->
    Term.Map.fold map ~init:[]
      ~f:(fun ~key ~data acc -> ([s, (l, key)], data) :: acc)
  | (s, (l, map)) :: tl ->
    let tail_bounds = bound_combinations_alist tl in
    Term.Map.fold map ~init:[]
      ~f:(fun ~key ~data acc ->
        let term, logic = key, data in
        List.fold tail_bounds ~init:acc
          ~f:(fun acc (lst, logic') ->
          ((s, (l, term)) :: lst, Logic.combine logic logic') :: acc))

let rec merge_records left right logic =
  let result = ref [String.Map.empty, logic] in
  String.Map.iter2 left right ~f:(fun ~key ~data ->
    let add l t =
      List.map !result ~f:(fun (map, logic) ->
        String.Map.add map ~key ~data:(l, t), Logic.And (l, logic)) in
      match data with
      | `Left (l, t)
      | `Right (l, t) ->
        result := add l t
      | `Both ((l, t), (l', t')) ->
        let res1 = add l t in
        let res2 = add l' t' in
        result := res1 @ res2);
    !result

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
      List.map (bound_combinations_list l) ~f:(fun (t, l) -> Tuple t, l) in
    let result = Term.Map.of_alist_exn term_list in
    result
  | List (x, s) ->
    let l = List.map x ~f:(fun x -> bound_terms_exn bound constrs x logic) in
    let term_list = bound_combinations_list l in
    begin
      match s with
      | None ->
        Term.Map.of_alist_exn
          (List.map term_list ~f:(fun (t, l) -> List (t, None), l))
      | Some var ->
        let bounds = bound_terms_exn bound constrs (Var var) logic in
        let lst = List.fold term_list ~init:[] ~f:(fun acc (head, logic') ->
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
  | Record (map, s) ->
    let b = String.Map.map map
      ~f:(fun (l, t) -> l, bound_terms_exn bound constrs t logic) in
    let term_map = bound_combinations_alist (String.Map.to_alist b) in
    begin
      match s with
      | None ->
        let combined = List.map term_map
          ~f:(fun (lst, logic) ->
          Record (String.Map.of_alist_exn lst, None), logic) in
        Term.Map.of_alist_exn combined
      | Some var ->
        let bounds = bound_terms_exn bound constrs (Var var) logic in
        let data = List.map term_map ~f:(fun (lst, logic) ->
          String.Map.of_alist_exn lst, logic) in
        let combined = List.fold data ~init:[] ~f:(fun acc (head, logic') ->
          Term.Map.fold bounds ~init:acc ~f:(fun ~key ~data acc ->
          match key with
          | Term.Record (map, None) ->
            let lst = merge_records head map logic' in
            lst @ acc
          | Term.Record (map, _) ->
              raise (Unsatisfiability_Error
                (Printf.sprintf "expected a ground list term, but %s found"
                  (Term.to_string key)))
          | _ -> acc)) in
        let l = List.map combined
          ~f:(fun (lst, logic) -> Record (lst, None), logic) in
        Term.Map.of_alist_exn l
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
          let b = Logic.Not (Logic.And (data, logic_constr)) in
          (constrs, Logic.Set.add logic b), acc)

(*
let poly_var_to_map bound context initial_map var logic_constr =
  match var with
  | None -> context, [initial_map]
  | Some v ->
    let constrs, logic = context in
    let bounds = bound_terms_exn bound constrs (Term.Var v) logic_constr in
    Term.Map.fold bounds ~init:(context, [])
      ~f:(fun ~key ~data (context, acc) ->
        match key with
        | Term.Record (map,

*)
let set_list_constraints context map =
  Term.Map.fold map ~init:context ~f:(fun ~key ~data (constrs, logic) ->
    match key with
    | Term.List _
    | Term.Nil -> constrs, logic
    | _ -> constrs, Logic.Set.add logic (Logic.Not data))

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
        let leftm = bound_terms_exn `Upper constrs term_left logic_left in
        let constrs = set_bound_exn (depth + 1) `Lower constrs s' leftm in
        constrs, logic
    (* atomic terms *)
    | (Nil | Int _ | Symbol _), Var s ->
      let leftm = bound_terms_exn `Upper constrs term_left logic_left in
      if Poly.(bound = `Upper) then
        let rightm = bound_terms_exn bound constrs term_right logic_right in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else
        let constrs = set_bound_exn (depth + 1) bound constrs s leftm in
        constrs, logic
    | Var s, (Nil | Int _ | Symbol _) ->
      let rightm = bound_terms_exn bound constrs term_right logic_right in
      if Poly.(bound = `Lower) then
        let leftm = bound_terms_exn `Upper constrs term_left logic_left in
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
        let bounds = bound_terms_exn `Upper constrs term_left logic_left in
        let constrs = set_bound_exn (depth + 1) bound constrs s bounds in
        constrs, logic
    | Var s, Tuple t ->
      if Poly.(bound = `Lower) then
        let solve ~key ~data acc =
          let left = key, data in
          solve_senior (depth + 1) bound context left right in
        let leftm = bound_terms_exn `Upper constrs term_left logic_left in
        Term.Map.fold leftm ~init:context ~f:solve
      else
        let bounds = bound_terms_exn bound constrs term_right logic_right in
        let constrs = set_bound_exn (depth + 1) bound constrs s bounds in
        constrs, logic
    (* list processing *)
    | List _, Var v ->
      if Poly.(bound = `Upper) then
        let bounds = bound_terms_exn bound constrs term_right logic_right in
        Term.Map.fold bounds ~init:context ~f:(fun ~key ~data acc ->
          solve_senior (depth + 1) bound context left (key, data))
      else
        let bounds = bound_terms_exn `Lower constrs term_left logic_left in
        let constrs = set_bound_exn (depth + 1) bound constrs v bounds in
        constrs, logic
    | Var v, List _ ->
      if Poly.(bound = `Lower) then
        let bounds = bound_terms_exn `Upper constrs term_left logic_left in
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
        let tail_list = bound_combinations_list tail_bounds in
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
        (* set constraints on type of term for polymorphic variable *)
        let context =
          match var with
          | None -> context
          | Some v ->
            let b = bound_terms_exn `Lower constrs (Var v) logic_left in
            set_list_constraints context b in
        let tail_bounds = List.map reml ~f:(fun x ->
          bound_terms_exn `Upper constrs x logic_left) in
        let tail_list = bound_combinations_list tail_bounds in
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
        (* set constraints on type of term for polymorphic variable *)
        let context =
          match var with
          | None -> context
          | Some v ->
            let b = bound_terms_exn `Lower constrs (Var v) logic_left in
            set_list_constraints context b in
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
    (* record processing *)
    | Record _, Var s ->
      if Poly.(bound = `Upper) then
        let bounds = bound_terms_exn bound constrs term_right logic_right in
        Term.Map.fold bounds ~init:context ~f:(fun ~key ~data acc ->
          solve_senior (depth + 1) bound context left (key, data))
      else
        let bounds = bound_terms_exn `Lower constrs term_left logic_left in
        let constrs = set_bound_exn (depth + 1) bound constrs s bounds in
        constrs, logic
    | Var s, Record _ ->
      if Poly.(bound = `Lower) then
        let bounds = bound_terms_exn `Upper constrs term_left logic_left in
        Term.Map.fold bounds ~init:context ~f:(fun ~key ~data acc ->
          solve_senior (depth + 1) bound context (key, data) right)
      else
        let bounds = bound_terms_exn bound constrs term_right logic_right in
        let constrs = set_bound_exn (depth + 1) bound constrs s bounds in
        constrs, logic
    | Record (map, var), Nil ->
      begin
        let context = String.Map.fold map ~init:context
          ~f:(fun ~key ~data acc ->
          let l, t = data in
          solve_senior (depth + 1) bound acc (t, l) right) in
        match var with
        | None -> context
        | Some v ->
          solve_senior (depth + 1) bound context (Var v, logic_left) right
      end
    | Nil, Record (map, var) ->
      begin
        let context = String.Map.fold map ~init:context
          ~f:(fun ~key ~data acc ->
          let l, t = data in
          solve_senior (depth + 1) bound acc left (t, l)) in
        match var with
        | None -> context
        | Some v ->
          solve_senior (depth + 1) bound context left (Var v, logic_left)
      end
    | Record (r, v), Record (r', v') ->
      begin
        if Poly.(bound = `Upper) then
          let bounds = bound_terms_exn bound constrs term_right logic_right in
          (* set bounds for all terms from the left to nil *)
          let context = String.Map.fold r ~init:context
            ~f:(fun ~key ~data acc ->
              let (guard, term) = data in solve_senior (depth + 1) bound acc
                (term, Logic.combine guard logic_left)
                (Nil, logic_right)) in
          let ctx = ref context in
          let var_bounds = ref Term.Map.empty in
          Term.Map.iter bounds ~f:(fun ~key ~data ->
            let logic = Logic.combine data logic_right in
            match key with
            | Record (r', None) ->
              begin
              let var_rec = ref String.Map.empty in
              let var_logic = ref logic in
              String.Map.iter r' ~f:(fun ~key ~data ->
                let label, (guard, term) = key, data in
                match String.Map.find r key with
                | None -> var_rec := String.Map.add !var_rec ~key:label
                  ~data:(Logic.combine guard logic, term);
                  var_logic := Logic.combine !var_logic (Logic.Not guard)
                | Some (guard', term') ->
                  try
                    ctx := solve_senior (depth + 1) bound !ctx (term', guard')
                      (term, guard);
                    var_logic := Logic.combine !var_logic
                      (Logic.Or [Logic.Not guard; guard'])
                  with Unsatisfiability_Error _ ->
                    var_logic := Logic.combine !var_logic
                      (Logic.combine (Logic.Not guard) (Logic.Not guard')));
                var_bounds := Term.Map.add !var_bounds ~key:(Record(!var_rec, None)) ~data:!var_logic
              end 
            | _ -> failwith "invalid term");
            let constrs, logic = !ctx in
            match v with
            | None -> constrs, logic
(*             raise (Incomparable_Terms (term_left, term_right)) *)
            | Some var ->
              let constrs = set_bound_exn (depth + 1) bound constrs var !var_bounds in
              constrs, logic
        else
          let bounds = bound_terms_exn bound constrs term_left logic_left in
          let ctx = ref context in
          let var_bounds = ref Term.Map.empty in
          Term.Map.iter bounds ~f:(fun ~key ~data ->
            let logic = Logic.combine data logic_left in
            match key with
            | Record (r, None) ->
              begin
              let var_rec = ref String.Map.empty in
              let var_logic = ref logic in
              String.Map.iter r ~f:(fun ~key ~data ->
                let label, (guard, term) = key, data in
                match String.Map.find r' key with
                | None -> var_rec := String.Map.add !var_rec ~key:label
                  ~data:(Logic.combine guard logic, term);
                  var_logic := Logic.combine !var_logic (Logic.Not guard)
                | Some (guard', term') ->
                  try
                    ctx := solve_senior (depth +1) bound !ctx (term, guard)
                      (term', guard');
                    var_logic := Logic.combine !var_logic
                      (Logic.Or [Logic.Not guard; guard'])
                  with Unsatisfiability_Error _ ->
                    var_logic := Logic.combine !var_logic
                      (Logic.combine (Logic.Not guard) (Logic.Not guard')));
                var_bounds := Term.Map.add !var_bounds ~key:(Record(!var_rec,None)) ~data:!var_logic
              end
            | _ -> failwith "invalid term");
            let constrs, logic = !ctx in
            match v' with
            | None -> constrs, logic
(*             raise (Incomparable_Terms (term_left, term_right)) *)
            | Some var ->
              let constrs = set_bound_exn (depth + 1) bound constrs var !var_bounds in
              constrs, logic

(*
      let module SM = String.Map in
      let module SS = String.Set in
      (* resolve terms that are associated with the same labels in both maps.
         E.g. from {a, b, c, d | $x} and {b, c, e, f | $y} terms with labels b
         and c will be removed. *)
      let set, set' = SS.of_list (SM.keys r), SS.of_list (SM.keys r') in
      let solve context l =
        let (l1, t1), (l2, t2) = SM.find_exn r l, SM.find_exn r' l in
        solve_senior (depth + 1) bound context (t1, l1) (t2, l2) in
      let context = SS.fold ~init:context ~f:solve (SS.inter set set') in
      let diff, diff' = SS.diff set set', SS.diff set' set in
      (* In records (choices) all labels are specified in the right (left) term
         must be also present in the left (right) term, otherwise this is an error.
         E.g. {a, b, c, d} <= {a, b, c, e | $x } -- left term lacks e *)
      let _ = if Poly.(v = None && not (SS.is_empty diff')) then
        let ts1, ts2 = Term.to_string term_left, Term.to_string term_right in
        unsat_error (Printf.sprintf "term %s contains labels that are not \
        present in term %s" ts2 ts1) in
      if Poly.(bound = `Upper) then
        if Poly.(v' = None) then context
        else
          let modified = ref r' in
          SS.iter set' ~f:(fun x -> modified := SM.remove !modified x);
          let record = Record (!modified, v') in
          let bounds = bound_terms_exn bound constrs record logic_right in
          let bounds = Term.Map.ch
          context
        else
        context
*)
      end
    (* switch processing *)
    | Switch lm, Var s ->
      if Poly.(bound = `Upper) then
        let rightm = bound_terms_exn bound constrs term_right logic_right in
        let leftm = Term.logic_map_to_term_map lm in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else
        let leftm = bound_terms_exn `Upper constrs term_left logic_left in
        let constrs = set_bound_exn (depth + 1) `Lower constrs s leftm in
        constrs, logic
    | Var s, Switch lm ->
      if Poly.(bound = `Lower) then
        let leftm = bound_terms_exn `Upper constrs term_left logic_left in
        let rightm = Term.logic_map_to_term_map lm in
        solve_senior_multi_exn (depth + 1) bound context leftm rightm
      else 
        let rightm = bound_terms_exn bound constrs term_right logic_right in
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
