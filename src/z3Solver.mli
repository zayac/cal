
val find_model : Z3.context -> Z3.ast -> Z3.model option

val mk_var : Z3.context -> string -> Z3.ast

val ast_from_logic : Z3.context -> Logic.Set.t -> Z3.ast

val evaluate : Z3.context -> Z3.model -> Logic.t -> bool
