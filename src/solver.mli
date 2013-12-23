open Core.Std

(** Constraints for collection terms *)
type collection_constr =
  | RecordWoLabels of String.Set.t (** a record that must not contain labels
    specified in the set *)
  | ChoiceWoLabels of String.Set.t (** a choice that must not contain labels
    specified in the set *)
  | ListCol

(** A constraint on variable *)
type var_constr =
  {
    bounds     : Term.t option * Term.t option; (** greatest lower and
      least upper bounds *)
    collection : collection_constr option; (** constraints for collection
      terms *)
  }

(** The exception is thrown when it is found that the network has unsatisfied
    constraints. *)
exception Unsatisfiability_Error of string

(** A unification procedure that finally returns unified constraints on
    variables. *)
val unify_exn : Network.G.t -> var_constr String.Map.t
