open Core.Std

type t =
  | False
  | True
  | Not of t
  | And of t * t
  | Or of t list
  | Var of string

val compare_t : t -> t -> int
val t_of_sexp : Sexplib.Sexp.t -> t
val sexp_of_t : t -> Sexplib.Sexp.t

include Comparable.S with type t := t

val hash : t -> int

val to_string : t -> string

val is_ground : t -> bool

val combine : t -> t -> t
