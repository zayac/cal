%{
open Term

let bool_constrs = ref []

let generate_pairs l =
  let rec apply acc el = function
  | [] -> acc
  | hd :: tl -> apply ((el, hd) :: acc) el tl in
  let rec iter_left acc = function
  | [] -> acc
  | hd :: tl -> iter_left (apply acc hd tl) tl in
  iter_left [] l

(* convert a label-term association list into a correct map structure with
   label conflict resolution. New constraints can be added to [bool_constrs]
   list while resolving constraints. *)
let map_of_alist l =
  let open Core.Std in
  let multi_map = String.Map.of_alist_multi l in
  let rec f (gacc: Term.t list) (vacc: Term.t list) = function
  | [] -> failwith "a list must contain at least one element"
  | (g, v) :: [] ->
    if not (List.is_empty gacc) then
      let gacc, vacc = g :: gacc, v :: vacc in
      let andl = List.map ~f:(fun (x, y) -> and_t x y) (generate_pairs gacc) in
      let _ = bool_constrs :=
        (andl, [Nil]) :: ([Nil], andl) :: !bool_constrs in
      (or_t gacc, or_t (List.map2_exn ~f:and_t gacc vacc))
    else
      g, v
  | (g, v) :: tl -> f (g :: gacc) (v :: vacc) tl in
  String.Map.map ~f:(f [] []) multi_map
%}

%token <int> INT
%token <string> VAR
%token <string> ID
%token NIL
%token LBRACE RBRACE LPAREN RPAREN LBRACKET RBRACKET LSMILE RSMILE
%token SCOLON COLON COMMA BAR LEQ EOF

%start <Constr.t list> parse
%%

parse:
  | constrs* EOF { $1 @ !bool_constrs }

constrs:
  | term+ LEQ term+ SCOLON { $1, $3 }
  | error
    {
      let open Errors in
      parse_error "Invalid constraint" $startpos $endpos }

term:
  | NIL { Nil }
  | INT { Int $1 }
  | ID { Symbol $1 }
  | VAR { Var $1 }
  | LPAREN term+ RPAREN { Tuple $2 }
  | LSMILE RSMILE
    {
      let open Core.Std in
      Choice (String.Map.empty, None)
    }
  | LBRACE RBRACE { Nil }
  | LBRACKET RBRACKET { Nil }
  | LSMILE separated_nonempty_list(COMMA, rec_entry) rec_list_tail? RSMILE
    {
      Choice (map_of_alist $2, $3)
    }
  | LBRACE separated_nonempty_list(COMMA, rec_entry) rec_list_tail? RBRACE
    {
      Record (map_of_alist $2, $3)
    }
  | LBRACKET separated_nonempty_list(COMMA, term) rec_list_tail? RBRACKET
    { List ($2, $3) }

rec_entry:
  | ID rec_guard? COLON term
    {
      let t = match $2 with
      | None -> Tuple [Symbol "not"; Nil]
      | Some x -> x in
      $1, (t, $4)
    }
  | error
    { let open Errors in
      parse_error "Invalid record entry" $startpos $endpos
    }

rec_guard:
  | LPAREN term RPAREN { $2 }

rec_list_tail:
  | BAR VAR { $2 }
