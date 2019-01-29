open Tree;;
open Buffer;;
open Printf;;
open List;;

type system_type = 
  | Impl of system_type * system_type
  | Var of string;;

type equation = Equality of system_type * system_type;;
type system = equation list;;

type tpair = TPair of system * system_type;;

let cnt = ref 0;;
let inc () = cnt := !cnt + 1; !cnt;;

let make_var () = "a" ^ (string_of_int (inc ()));;

let get_system tpair = match tpair with
  | TPair (system, t) -> system;;

let get_type tpair = match tpair with
  | TPair (system, t) -> t;;

let set_system tree = 
  let rec walk token = match token with 
    | Abstr (x, p)  ->  let p_pair = walk p in
                          let new_var = Var (make_var ()) in
                            TPair (
                              get_system p_pair,
                              Impl (new_var, (get_type p_pair)))
    | Apply (p, q)  ->  let p_pair = walk p in
                          let q_pair = walk q in
                            let new_var = Var (make_var ()) in
                              let p_type = get_type p_pair in
                              let p_system = get_system p_pair in
                                let q_type = get_type q_pair in
                                let q_system = get_system q_pair in
                                  TPair (
                                    (Equality (p_type, (Impl (q_type, new_var)))) ::
                                    (p_system @ q_system),
                                  new_var)
    | Var x         ->  let new_var = Var (make_var ()) in
                        TPair ([], new_var)
  in walk tree;;

let (>>) x f = f x;;

let input = read_line ();;
let input_tree = input >> Lexing.from_string >> Parser.main Lexer.main;;