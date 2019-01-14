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


let input = read_line ();;

let (>>) x f = f x;;
input >> Lexing.from_string >> Parser.main Lexer.main >> string_of_tree >> print_string;;