open Core.Std

(** Constraints for collection terms *)
type collection_constr =
  | RecordWoLabels of String.Set.t (** a record that must not contain labels
    specified in the set *)
  | ChoiceWoLabels of String.Set.t (** a choice that must not contain labels
    specified in the set *)
  | List

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

(** [add_list_cstr_exn cm v] adds a new constraint to map of constraints [cm]
    setting variable [v] to a list term. Throws [Unsatisfiability_Error] if a
    conflicting constraint is found. *)
val add_list_cstr_exn : var_constr String.Map.t -> string
  -> var_constr String.Map.t

(** [add_record_cstr_exn cm v] adds a new constraint to map of constraints [cm]
    setting variable [v] to a record term. Throws [Unsatisfiability_Error] if a
    conflicting constraint is found. *)
val add_record_cstr_exn : var_constr String.Map.t -> string
  -> String.Set.t -> var_constr String.Map.t

(** [add_choice_cstr_exn cm v] adds a new constraint to map of constraints [cm]
    setting variable [v] to a choice term. Throws [Unsatisfiability_Error] if a
    conflicting constraint is found. *)
val add_choice_cstr_exn : var_constr String.Map.t -> string
  -> String.Set.t -> var_constr String.Map.t

(** A unification procedure that finally returns unified constraints on
    variables. *)
val unify_exn : Network.G.t -> var_constr String.Map.t
