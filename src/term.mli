open Core.Std

(** A generic non-ground term in AKTA *)
type term =
  | Nil
  | Int of int
  | Symbol of string
  | Tuple of term list
  | List of term list * string option
  | Record of (term * term) String.Map.t * string option
  | Choice of (term * term) String.Map.t * string option
  | Var of string

(** Functions over terms *)
module Term : sig
  type t = term

  (** Lexicographical term comparison *)
  include Comparable.S with type t := t

  (** Convert term to syntaxical representation *)
  val to_string : t -> string
  (** Parse term expression from string *)
  val of_string : string -> t

  (** [is_nil t] returns [true] only if a term [t] is ground and equals to
      [Nil] in the canonical form.
      Otherwise, it returns [false] for ground term.
      If [t] is not ground, then it throws an exception *)
  val is_nil_exn : t -> bool
  (** [is_nil t] does the same that [is_nil_exn t] does, but without throwing
      an exception. It returns [None] instead. *)
  val is_nil : t -> bool option

  (** [is_ground t] returns [true] only if term [t] does not contain term of
      the form [Var s] as children. *)
  val is_ground : t -> bool

  (** Provided a term [t], [canonize t] reduces it to the canonical
      form. Terms with variables [Var s] are not reduced. *)
  val canonize : t -> t

  (** [seniority t t'] compares two ground terms using the seniority relation.
      Throws an exception if one of the terms is not ground. *)
  val seniority_exn : t -> t -> int

  (** [vars t] returns a set of all variable strings [s] from terms of the
      form [Var s] that are contained in [t]. *)
  val vars : t -> String.Set.t
end
