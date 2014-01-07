open Core.Std

(** A generic non-ground term in AKTA *)
type t =
  | Nil
  | Int of int
  | Symbol of string
  | Tuple of t list
  | List of t list * string option
  | Record of (t * t) String.Map.t * string option
  | Choice of (t * t) String.Map.t * string option
  | Var of string

val compare_t : t -> t -> int
val t_of_sexp : Sexplib.Sexp.t -> t
val sexp_of_t : t -> Sexplib.Sexp.t

(** This exception must be raised every time when non-ground term is 
    provided as an argument for a function that expects a ground term. *)
exception Non_Ground of t with sexp

(** The exception is raised when the seniority relation is being resolved
    for two incomparable terms. *)
exception Incomparable_Terms of t * t with sexp

(** Lexicographical term comparison *)
include Comparable.S with type t := t

(** A hash function for a term *)
val hash : t -> int

(** Convert term to syntaxical representation *)
val to_string : t -> string

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

(** [get_vars t] returns a set of variable strings [s] from terms
    of the form [Var s] that are contained in [t] *)
val get_vars : t -> String.Set.t

(** [get_external_vars t] returns a set of variable strings [s] from terms
    of the form [Var s] that are contained in [t] and are not part of any
    boolean expression (e.g. is part of tuples (not ...), (or ...), (and ...).
    *)
val get_external_vars : t -> String.Set.t

(** [is_not t] converts a term [t] to the term [(not t)] *)
val not_t : t -> t
(** [or_t tl] converts a list of terms [tl] to the term [(or tl)] *)
val or_t : t list -> t
(** [and_t t t'] converts terms [t] and [t'] to the term [(and t t')] *)
val and_t : t -> t -> t

(** checks either a term is a 'not' logical expression *)
val is_not : t -> bool
(** checks either a term is an 'or' logical expression *)
val is_or : t -> bool
(** checks either a term is an 'and' logical expression *)
val is_and : t -> bool
(** checks either a term is a logical expression *)
val is_logic : t -> bool

(** checks either a term contains some logical expression inside (or is a
    logical expression itself) *)
val contains_logic : t -> bool
