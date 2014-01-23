open Core.Std

(** The exception is thrown when it is found that the network has unsatisfied
    constraints. *)
exception Unsatisfiability_Error of string

(** A unification procedure that finally returns unified variable constraints
    as well as logical constraints that need to be unified. *)
val unify_exn : Network.G.t -> Constr.var_bounds String.Map.t * Logic.Set.t
