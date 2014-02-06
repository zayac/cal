open Core.Std

module T = struct
  type t =
    | False
    | True
    | Not of t
    | And of t * t
    | Or of t list
    | Var of string
  with sexp, compare
end
include T
include Comparable.Make(T)

let hash = Hashtbl.hash

let rec to_string t =
  let module L = List in
  let module S = String in
  match t with
  | False -> "false"
  | True -> "true"
  | Not t -> Printf.sprintf "(not %s)" (to_string t)
  | And (t, t') -> Printf.sprintf "(and %s %s)" (to_string t)
    (to_string t')
  | Or tl ->
    Printf.sprintf "(or %s)" (S.concat ~sep:" " (L.map ~f:to_string tl))
  | Var v -> "$" ^ v

let rec is_ground = function
  | False | True -> true
  | Not t -> is_ground t
  | And (t, t') -> is_ground t && is_ground t'
  | Or tl -> List.for_all ~f:is_ground tl
  | Var _ -> false

let combine t t' =
  if t = True || t = t' then t'
  else if t' = True then t
  else And (t, t')

let pairwise_not_and l =
  let generate_pairs l =
    let rec apply acc el = function
    | [] -> acc
    | hd :: tl -> apply ((el, hd) :: acc) el tl in
    let rec iter_left acc = function
    | [] -> acc
    | hd :: tl -> iter_left (apply acc hd tl) tl in
    iter_left [] l in
  List.map ~f:(fun (x, y) -> Not (And (x, y))) (generate_pairs l)

