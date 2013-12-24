open Core.Std

let rec union =
  let open Term in
  let create_union t1 t2 = Tuple [Symbol "union"; t1; t2] in
  function
  | Tuple [Symbol "union"; t; t'] as el ->
    begin
      match t, t' with
      | List (l, None), List (l', v') -> List (l @ l', v')
      | Record(m, None), Record (m', v') ->
        Record (String.Map.merge m m' ~f:(fun ~key -> function
          | `Both ((g1, t1), (g2, t2)) ->
             Some (create_union g1 g2, create_union t1 t2)
          | `Left v
          | `Right v -> Some v
          ), v')
      | _ -> el
    end
  | t -> t
