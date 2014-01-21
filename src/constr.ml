open Core.Std

module T = struct
  type t = Term.t list * Term.t list with sexp, compare
end
include T
include Comparable.Make(T)

type collection = 
  {
    record: (Logic.t * Logic.t String.Map.t) option;
    choice: (Logic.t * Logic.t String.Map.t) option;
    lst: Logic.t option;
  }
with sexp

type var =
  {
    bounds : Logic.t Term.Map.t * Logic.t Term.Map.t;
    typ : collection;
  }
with sexp

let hash = Hashtbl.hash

let default = [], []

let to_string (l, r) =
  let f x = String.concat ~sep:", " (List.map ~f:Term.to_string x) in
  String.concat ~sep:" <= " [f l; f r]

(*
let print_vars constrs =
  String.Map.iter ~f:(fun ~key ~data ->
    Printf.printf "Constraints for variable %s:\n" key;
    let glb, lub = data.bounds in
    let str x =
      let alist = Logic.Map.to_alist x in
      let sl = List.map
        ~f:(fun (g, t) -> Printf.sprintf "%s: %s" (Logic.to_string g)
          (Term.to_string t)) alist in
        String.concat ~sep:", " sl in
    let print_col = function
      | RecordWoLabels s ->
        "R" ^ (List.to_string ~f:(fun (l, s) -> (Logic.to_string l) ^ ":" ^ s)
          (Logic.Map.to_alist s))
      | ChoiceWoLabels s ->
        "C" ^ (List.to_string ~f:(fun (l, s) -> (Logic.to_string l) ^ ":" ^ s)
          (Logic.Map.to_alist s))
      | ListCol -> "L" in
    Printf.printf"\tbounds: ({%s}, {%s})\n\tcollection: {%s}\n"
      (str glb) (str lub)
      (print_col data.collection)) constrs
*)

let get_vars (l, r) =
  let f = List.fold_left ~init:String.Set.empty
    ~f:(fun s x -> String.Set.union s (Term.get_vars x)) in
  f l, f r
