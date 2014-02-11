open Core.Std

module T = struct
  type t = Term.t list * Term.t list with sexp, compare
end
include T
include Comparable.Make(T)

(** A constraint on variable *)
type var_bounds = Logic.t Term.Map.t * Logic.t Term.Map.t

let hash = Hashtbl.hash

let default = [], []

let to_string (l, r) =
  let f x = String.concat ~sep:", " (List.map ~f:Term.to_string x) in
  String.concat ~sep:" <= " [f l; f r]

let get_vars (l, r) =
  let f = List.fold_left ~init:String.Set.empty
    ~f:(fun s x -> String.Set.union s (Term.get_vars x)) in
  f l, f r

let is_valid c =
  if Int.(Term.Map.length c = 1) && Poly.(Term.Map.data c = [Logic.True]) then
    Some (List.hd_exn (Term.Map.keys c))
  else
    None

let print_constraints map =
  let constr_to_string c =
    let l = Term.Map.to_alist c in
    let sl = List.map l
      ~f:(fun (t, l) ->
        if Logic.(l <> Logic.True) then
          Printf.sprintf "[%s]%s" (Logic.to_string l) (Term.to_string t)
        else Printf.sprintf "%s" (Term.to_string t)) in
    String.concat ~sep:", " sl in
  let print_bound ~key ~data =
    let l, u = data in
    Printf.printf "%s <= %s <= %s\n" (constr_to_string l) key
      (constr_to_string u) in
  String.Map.iter ~f:print_bound map

