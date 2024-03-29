open Core.Std

let rec union =
  let open Term in
  let create_union t1 t2 = Tuple [Symbol "union"; t1; t2] in
  let bool_constrs = ref Logic.True in
  function
  | Tuple [Symbol "union"; t; t'] as el ->
    begin
      match t, t' with
      | List (l, None), List (l', v') -> List (l @ l', v'), !bool_constrs 
      | Record(m, None), Record (m', v') ->
        Record (String.Map.merge m m' ~f:(fun ~key -> function
          | `Both ((g1, t1), (g2, t2)) ->
            bool_constrs :=
              Logic.combine !bool_constrs (Logic.Not (Logic.combine g1 g2));
            Some (Logic.Or [g1; g2], create_union t1 t2)
          | `Left v
          | `Right v -> Some v
          ), v'), !bool_constrs 
      | _ -> el, !bool_constrs 
    end
  | t -> t, !bool_constrs 
