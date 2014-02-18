open Core.Std

let find_model ctx ast =
  let slv = Z3.mk_solver ctx in
  Z3.solver_assert ctx slv ast;
  match Z3.solver_check ctx slv with
  | Z3.L_FALSE
  | Z3.L_UNDEF -> None
  | Z3.L_TRUE -> Some (Z3.solver_get_model ctx slv)

 
let mk_var ctx name =
  Z3.mk_const ctx (Z3.mk_string_symbol ctx name) (Z3.mk_bool_sort ctx)

let model_to_ast ctx model =
  let assignments = List.map ~f:(String.split ~on:' ')
    (String.split ~on:'\n' (Z3.model_to_string ctx model)) in
  let values = List.map
    ~f:(function
      | [v; _; "false"] -> Z3.mk_not ctx (mk_var ctx v)
      | [v; _; "true"] -> mk_var ctx v
      | _ -> failwith "error") assignments in
  Z3.mk_not ctx (Z3.mk_and ctx (Array.of_list values)) 

let find_all_models ctx ast =
  let models = ref [] in
  let result = ref (find_model ctx ast) in
  let ast' = ref ast in
  while !result <> None do
    (* add model to the list of solutions *)
    let value = Option.value_exn !result in
    models := value :: !models;
    (* add a new constraint *)
    ast' := Z3.mk_and ctx (Array.append [| !ast' |]
      [| model_to_ast ctx value |]);
    result := find_model ctx !ast';
  done;
  !models

let ast_from_logic ctx l =
  let open Logic in
  let rec transform ctx = function
  | False -> Z3.mk_false ctx
  | True -> Z3.mk_true ctx
  | Not x -> Z3.mk_not ctx (transform ctx x)
  | And (x, x') -> Z3.mk_and ctx [| (transform ctx x); (transform ctx x') |]
  | Or x -> Z3.mk_or ctx (Array.of_list (List.map ~f:(transform ctx) x))
  | Var v -> mk_var ctx v in
  let logic_list = Logic.Set.to_list l in
  let ast_list = List.map ~f:(transform ctx) logic_list in
  Z3.mk_and ctx (List.to_array ast_list)

let evaluate ctx model l =
  let ast = ast_from_logic ctx (Logic.Set.singleton l) in
  let result = Z3.model_eval ctx model ast true in
  match result with
  | None -> failwith "something wrong"
  | Some ast' ->
    let b = Z3.get_bool_value ctx ast' in
      if b = Z3.L_TRUE then true
      else if b = Z3.L_FALSE then false
      else failwith "something wrong"
