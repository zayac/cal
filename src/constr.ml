open Core.Std

module T = struct
  type t = Term.t list * Term.t list with sexp, compare 
end
include T
include Comparable.Make(T)

type collection =
  | RecordWoLabels of String.Set.t
  | ChoiceWoLabels of String.Set.t
  | ListCol
with sexp

type var =
  {
    bounds     : Term.t option * Term.Set.t * Term.t option * Term.Set.t;
    collection : collection option;
  }
with sexp

let hash = Hashtbl.hash

let default = [], []

let to_string (l, r) =
  let f x = String.concat ~sep:", " (List.map ~f:Term.to_string x) in
  String.concat ~sep:" <= " [f l; f r]

let print_vars constrs =
  String.Map.iter ~f:(fun ~key ~data ->
    Printf.printf "Constraints for variable %s:\n" key; 
    let ground1, set1, ground2, set2 = data.bounds in
    Printf.printf"\tbounds: (%s, {%s}, %s, {%s})\n\tcollection: %s\n"
      (Option.value_map ~default:"none" ~f:Term.to_string ground1)
      (String.concat ~sep:", " (List.map ~f:Term.to_string (Term.Set.to_list set1)))
      (Option.value_map ~default:"none" ~f:Term.to_string ground1)
      (String.concat ~sep:", " (List.map ~f:Term.to_string (Term.Set.to_list set1)))
      (match data.collection with 
      | None -> "none"
      | Some (RecordWoLabels s) -> "record without " ^ (String.concat ~sep:", " (String.Set.to_list s))
      | Some (ChoiceWoLabels s) -> "choice without " ^ (String.concat ~sep:", " (String.Set.to_list s))
      | Some ListCol -> "list")) constrs

let get_vars (l, r) =
  let f = List.fold_left ~init:String.Set.empty
    ~f:(fun s x -> String.Set.union s (Term.get_vars x)) in
  f l, f r
