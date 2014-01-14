open Core.Std

(** A constraint for terms *)
type t = Term.t list * Term.t list

(** Constraints for collection terms *)
type collection =
  | RecordWoLabels of String.Set.t (** a record that must not contain labels
    specified in the set *)
  | ChoiceWoLabels of String.Set.t (** a choice that must not contain labels
    specified in the set *)
  | ListCol

(** A constraint on variable *)
type var =
  {
    bounds     : Term.t option * Term.Set.t * Term.t option * Term.Set.t;
    (** greatest lower and least upper bounds. The first and the third argument
        represent bounds without any logical expressions, whether the second
        and the fourth argument are sets of bounds represented as logical
        expressions. *)
    collection : collection option; (** constraints for collection terms *)
  }

val compare_t : t -> t -> int
val t_of_sexp : Sexplib.Sexp.t -> t
val sexp_of_t : t -> Sexplib.Sexp.t

(** Lexicographical constraint comparison *)
include Comparable.S with type t := t

(** A hash function for a constraint *)
val hash : t -> int

(** The default value *)
val default : t

(** Convert contraint to syntaxical representation *)
val to_string : t -> string

(** print a set of constraints on variables *)
val print_vars : var String.Map.t -> unit

(** [vars t] returns two sets of variables from terms of the form [Vars s] in
    the left and right parts of the constraint. *)
val get_vars : t -> String.Set.t * String.Set.t

