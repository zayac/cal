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

type var =
  {
    bounds     : Term.t option * Term.Set.t * Term.t option * Term.Set.t;
    collection : collection option;
  }

let hash = Hashtbl.hash

let default = [], []

let to_string (l, r) =
  let f x = String.concat ~sep:", " (List.map ~f:Term.to_string x) in
  String.concat ~sep:" <= " [f l; f r]

let get_vars (l, r) =
  let f = List.fold_left ~init:String.Set.empty
    ~f:(fun s x -> String.Set.union s (Term.get_vars x)) in
  f l, f r

let get_external_vars (l, r) =
  let f = List.fold_left ~init:String.Set.empty
    ~f:(fun s x -> String.Set.union s (Term.get_external_vars x)) in
  f l, f r
