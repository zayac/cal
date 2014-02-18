
val find_model : Z3.context -> Z3.ast -> Z3.model option

val find_all_models : Z3.context -> Z3.ast -> Z3.model list

val mk_var : Z3.context -> string -> Z3.ast

val ast_from_logic : Z3.context -> Logic.Set.t -> Z3.ast

val evaluate : Z3.context -> Z3.model -> Logic.t -> bool
