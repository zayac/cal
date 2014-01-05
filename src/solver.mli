open Core.Std

(** The exception is thrown when it is found that the network has unsatisfied
    constraints. *)
exception Unsatisfiability_Error of string

(** A unification procedure that finally returns unified constraints on
    variables. *)
val unify_exn : Network.G.t -> Constr.var String.Map.t
