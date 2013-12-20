open Core.Std

module T = struct
  type t =
    | Nil
    | Int of int
    | Symbol of string
    | Tuple of t list
    | List of t list * string option
    | Record of (t * t) String.Map.t * string option
    | Choice of (t * t) String.Map.t * string option
    | Var of string
  with sexp, compare
end
include T
include Comparable.Make(T)

exception Non_Ground of t with sexp

exception Incomparable_Terms of t * t with sexp

let hash = Hashtbl.hash

let rec to_string t =
  let module L = List in
  let module S = String in
  let module SM = String.Map in
  let tail_to_string = function
  | None -> ""
  | Some v -> " | $" ^ v in
  let dict_el_to_string (l, (g, t)) =
    Printf.sprintf "%s(%s): %s" l (to_string g) (to_string t) in
  let print_dict x tail lsep rsep =
    let element_strs = L.map ~f:dict_el_to_string (SM.to_alist x) in
    S.concat [lsep;
      S.concat ~sep:", " element_strs; tail_to_string tail; rsep] in
  match t with
  | Nil -> "nil"
  | Int x -> string_of_int x
  | Symbol x -> x
  | Tuple x -> S.concat ["("; S.concat ~sep:", " (L.map ~f:to_string x); ")"]
  | List (x, tail) ->
    S.concat ["["; S.concat ~sep:", " (L.map ~f:to_string x); 
      tail_to_string tail; "]"]
  | Record (x, tail) -> print_dict x tail "{" "}"
  | Choice (x, tail) -> print_dict x tail "(:" ":)"
  | Var x -> "$" ^ x

let rec is_nil = function
  | Nil -> Some true
  | List (x, None) ->
    let nil_list = List.map ~f:is_nil x in
    if List.exists ~f:is_none nil_list then None
    else if List.exists ~f:(Poly.(=) (Some false)) nil_list then
      Some false
    else Some true
  | Record (x, None) ->
    let is_element_nil (g, t) =
      match is_nil g with
      | None | Some true -> None
      | Some false -> is_nil t in
    let nil_list = (List.map ~f:is_element_nil (String.Map.data x)) in
    if List.exists ~f:is_none nil_list then None
    else if List.exists ~f:(Option.value ~default:false) nil_list then
      Some false
    else Some true
  | Var _
  | List (_, Some _)
  | Record (_, Some _) -> None
  | Int _ | Symbol _ | Tuple _ | Choice (_, _) -> Some false

  let rec is_nil_exn t =
    try 
      match t with
      | Nil -> true
      | List (x, None) -> List.for_all ~f:is_nil_exn x
      | Record (x, None) ->
        let is_element_nil (g, t) =
          if is_nil_exn g then true
          else is_nil_exn t in 
        String.Map.for_all ~f:is_element_nil x 
      | Var _
      | List (_, Some _)
      | Record (_, Some _) -> raise (Non_Ground t)
      | Int _ | Symbol _ | Tuple _ | Choice (_, _)  -> false
    with Non_Ground _ -> raise (Non_Ground t)

let rec canonize t =
  let rec trim_list_rev = function
  | [] -> []
  | hd :: tl as el ->
    match is_nil hd with
    | Some true -> trim_list_rev tl
    | Some false | None -> el in
  match t with
  | List (x, None) -> List (List.rev (trim_list_rev (List.rev x)), None)
  | x -> x

let rec is_ground = function
  | Nil | Int _ | Symbol _ -> true
  | List (x, None)
  | Tuple x -> List.for_all ~f:is_ground x
  |  Record (x, None)
  | Choice (x, None) ->
    String.Map.for_all ~f:(fun (g, t) -> is_ground g && is_ground t) x
  | Choice (_, _)
  | Record (_, _)
  | List (_, _)
  | Var _ -> false

let rec seniority_exn t1 t2 =
  try
    let seniority_lists_exn l l' =
    let lhead = List.take l (List.length l') in
    let comp_res = List.map2_exn ~f:seniority_exn lhead l' in
    if List.exists ~f:(Int.(=) 1) comp_res then
        raise (Incomparable_Terms (t1, t2))
    else if Int.(List.length l = List.length l')
        && List.for_all ~f:(Int.(=) 0) comp_res then 0
    else 1 in
    match t1, t2 with
    | t1, t2 when t1 = t2 -> 0
    | Nil, x when is_nil_exn x -> 0
    | x, Nil when is_nil_exn x -> 0
    | _, Nil -> 1
    | Nil, _ -> -1
    | Tuple x, Tuple x' ->
      if Int.(List.length x <> List.length x') then
        raise (Incomparable_Terms (t1, t2))
      else
        let comp_res = List.map2_exn ~f:seniority_exn x x' in
        let less = List.exists ~f:(Int.(=) (-1)) comp_res in
        let more = List.exists ~f:(Int.(=) 1) comp_res in
        if less && more then raise (Incomparable_Terms (t1, t2))
        else if less then -1
        else if more then 1
        else 0
    | List (x, None), List (x', None) ->
      if Int.(List.length x > List.length x') then seniority_lists_exn x x'
        else -1 * (seniority_lists_exn x' x)
    | Record (x, None), Record (x', None)
    | Choice (x', None), Choice (x, None) -> seniority_maps_exn x x'
    | _ -> raise (Incomparable_Terms (t1, t2))
  with Incomparable_Terms _
     | Non_Ground _ ->
     raise (Incomparable_Terms (t1, t2))

(* [seniority_mapes exn x x'] resolves the seniority relation for two 'map'
    terms, where [x] and [x'] has types [(term * term) String.Map] each.
    Basically, this is a seniority relation resolution for record and choice
    terms. *)
and seniority_maps_exn x x' =
  let module SM = String.Map in
  let error_s = "wrong seniority relation" in
  let comp_res = ref [] in
  let validate map ~key ~data:(guard, term) =
    let guard', term' = SM.find_exn map key in
    seniority_exn guard' guard in
  let _ = if Int.(SM.length x > SM.length x') then
    SM.iter ~f:(fun ~key ~data -> 
      comp_res := (validate x ~key ~data) :: !comp_res
    ) x'
  else
    SM.iter ~f:(fun ~key ~data -> 
      comp_res := (validate x' ~key ~data) :: !comp_res
    ) x in
  let less = List.exists ~f:(Int.(=) (-1)) !comp_res in
  let more = List.exists ~f:(Int.(=) 1) !comp_res in
  if less && more then invalid_arg error_s
  else if less then -1
  else if more then 1
  else 0

let rec vars t =
  let module SS = String.Set in
  let module SM = String.Map in
  let module L = List in
  match t with
  | Var v -> String.Set.singleton v
  | Nil | Int _ | Symbol _ -> SS.empty
  | Tuple x -> L.fold_left ~init:SS.empty ~f:SS.union (L.map ~f:vars x)
  | List (x, tail) ->
    let tl = Option.value_map ~default:SS.empty ~f:SS.singleton tail in
    SS.union tl (L.fold_left ~init:SS.empty ~f:SS.union (L.map ~f:vars x))
  | Record (map, v)
  | Choice (map, v) ->
    let f ~key:_ ~data:(g, t) acc =
    SS.union acc (SS.union (vars g) (vars t)) in
    let tl = Option.value_map ~default:SS.empty ~f:SS.singleton v in
    SS.union tl (SM.fold ~init:SS.empty ~f:f map)

