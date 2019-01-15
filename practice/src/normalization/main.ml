open Tree;;
open Buffer;;
open Printf;;

let buffer_len = 1000000;;

let string_of_tree tree =
  let buff = create (buffer_len * 2) in
  let rec s_token token = match token with
    | Var v          -> add_string buff v
    | Apply (t1, t2) -> add_char   buff '(';
                        s_token t1;
                        add_char   buff ' ';
                        s_token t2;
                        add_char   buff ')'
    | Abstr (v, t)   -> add_string buff "(\\";
                        add_string buff v;
                        add_char   buff '.';
                        s_token t;
                        add_char   buff ')'
    | Nothing        -> add_string buff ""
  in s_token tree;
  contents buff;;

let make_name name = name ^ "'";;

let change_name expr old_v new_v =
  let rec walk token = match token with
    | Apply (t1, t2) -> Apply (walk (t1), walk (t2))
    | Abstr (v, t)   -> if v = old_v then Abstr (new_v, walk t)
                        else Abstr (v, walk t)
    | Var v          -> if (v = old_v) then Var new_v
                        else token
    | Nothing        -> token
  in walk expr;;

let do_reduction expr var in_expr = 
  let rec walk token = match token with
    | Abstr (v, t)   -> if v <> var then Abstr (v, walk t)
                      else Abstr (make_name (v), change_name (t, v, make_name (v)))
    | Apply (t1, t2) -> Apply (walk(t1), walk(t2))
    | Var v          -> if v = var then in_expr else token
    | Nothing        -> token
  in walk expr;;

let b_reduction tree = match tree with
    | Abstr (_, _)         -> tree
    | Var _                -> tree
    | Nothing              -> Nothing
    | Apply (expr1, expr2) -> match expr1 with
      | Abstr (v, expr) -> do_reduction expr v expr2
      | Apply (_, _)    -> tree
      | Var _           -> tree
      | Nothing         -> tree;;

let (>>) x f = f x;;
let input_tree = read_line () >> Lexing.from_string >> Parser.main Lexer.main;;

input_tree >> b_reduction >> string_of_tree >> print_string;;