open Tree;;
open Buffer;;
open Printf;;
open List;;
open Hashtbl;;

module StrSet = Set.Make(String);;

let (>>) x f = f x;;

type system_type = 
  | Impl of system_type * system_type
  | Var of string;;

type equation = Equality of system_type * system_type;;
type system = equation list;;

type tpair = TPair of system * system_type;;            

let get_eq_if b eq = match eq with
  | Equality (l, r) -> if b then r else l;;

let get_eq_left  = get_eq_if false;;
let get_eq_right = get_eq_if true;;

let get_eq_var eq = 
  let t = get_eq_left eq in match t with
    | Var x  -> x
    | Impl _ -> "";;

let get_system tpair = match tpair with
  | TPair (system, t) -> system;;

let get_type tpair = match tpair with
  | TPair (system, t) -> t;;

(* print block  *)

let print_type token =
  let rec walk t = match t with
    | Impl (v1, v2) -> print_string "(";
                        walk v1;
                        print_string " -> ";
                        walk v2;
                        print_string ")";
    | Var v         -> print_string v
  in walk token;;

let println_type t = print_type t;
  print_string "\n";;

let println_equation eq = match eq with
  | Equality (t1, t2) ->  print_type t1;
                          print_string " = ";
                          print_type t2;
                          print_string "\n";;

let print_system tpair = 
  let rec walk pair = match pair with
    | TPair (system, t) ->  println_type t;
                            List.iter (fun eq -> println_equation eq) system;
                            print_string "\n";
  in walk tpair;;

let string_of_tree tree =
  let buff = Buffer.create 100000 in
  let rec s_token token = match token with
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
    | Var v          -> add_string buff v
  in s_token tree;
  contents buff;;

let string_of_type t = 
  let buff = Buffer.create 10000 in
  let rec walk token = (match token with
    | Impl (p, q) -> add_char buff '(';
                     walk p;
                     add_string buff " -> ";
                     walk q;
                     add_char buff ')';
    | Var v       -> add_string buff v) 
  in walk t;
  contents buff;;

(* create system block *)

let cnt = ref 0;;
let clr () = cnt := 0
let inc () = cnt := !cnt + 1; !cnt;;

let make_var hash var = if Hashtbl.mem hash var then
                          Hashtbl.find hash var 
                        else 
                          let name = "t" ^ (string_of_int (inc ())) in
                            Hashtbl.add hash var name;
                            name;;    

let make_new_var () = "t" ^ (string_of_int (inc ()));;

let set_system tree = 
  let table = Hashtbl.create 100 in
  let rec walk token = match token with 
    | Abstr (x, p)  ->  let p_pair = walk p in
                          let new_var = Var (make_var table x) in
                            let t = TPair (
                              get_system p_pair,
                              Impl (new_var, (get_type p_pair))) in
                                Hashtbl.remove table x;
                                t;
    | Apply (p, q)  ->  let p_pair = walk p in
                          let q_pair = walk q in
                            let new_var = Var (make_new_var ()) in
                              let p_type = get_type p_pair in
                              let p_system = get_system p_pair in
                                let q_type = get_type q_pair in
                                let q_system = get_system q_pair in
                                  TPair (
                                    (Equality (p_type, (Impl (q_type, new_var)))) ::
                                    (p_system @ q_system),
                                  new_var)
    | Var x         ->  let new_var = Var (make_var table x) in
                          TPair ([], new_var)
  in walk tree;;

(* solve system block *)

let remove_equils system = 
  let is_removed eq = match eq with
    | Equality (t1, t2) -> match t1 with
      | Impl _  -> false
      | Var x   -> (match t2 with
        | Impl _  -> false
        | Var y   -> if x = y then true else false) in
    
    let rec loop s = match s with
      | el :: values  -> let next = loop values in
          if is_removed el then next else el :: next;
      | []            -> []
  in loop system;;

let swap_vars system = 
  let swap_eq eq = match eq with
    | Equality (t1, t2) -> (match t1 with
      | Var x   -> eq
      | Impl _  -> (match t2 with
        | Var y   -> Equality (t2, t1)
        | Impl _  -> eq)) in
    List.map (fun eq -> swap_eq eq) system;;

let reduction system =
  let do_reduction eq = (match eq with
    | Equality (t1, t2) -> match t1 with
      | Var _           -> [eq]
      | Impl (t11, t12) -> (match t2 with
        | Var _           -> [eq]
        | Impl (t21, t22) -> [Equality (t11, t21); Equality (t12, t22)])) in
    List.flatten (List.map (fun eq -> do_reduction eq) system);;

let insert system var token n =
  let rec walk t = match t with
    | Impl (t1, t2) -> Impl (walk t1, walk t2)
    | Var x         -> if x = var then token else t in
  let do_ins eq = Equality (walk (get_eq_left eq), walk (get_eq_right eq)) in

  let rec loop cur i = (match cur with
      | el :: values -> let eq = if i = n then el else do_ins el in
        eq :: (loop values (i + 1))
      | []           -> [])
  in loop system 0;;

let contain_var system var n =
  let rec walk token = (match token with
    | Impl (t1, t2) -> walk t1 || walk t2
    | Var x         -> var = x) in
  let eq_contain eq = (eq >> get_eq_left >> walk) || (eq >> get_eq_right >> walk) in

  let rec loop s i = match s with
    | el :: values -> if i <> n && eq_contain el
      then true
      else loop values (i + 1)
    | [] -> false
  in loop system 0;;

let substitution system = 
  let is_to_sub eq = (match eq with
    | Equality (t1, _) -> match t1 with
      | Impl _ -> false  
      | Var x  -> true) in 
  let rec loop cur_sys n = match cur_sys with
    | el :: values -> 
      if is_to_sub el then 
        let var = get_eq_var el in
          if contain_var system var n then
            let token = get_eq_right el in
              insert system var token n
          else loop values (n + 1)
      else
        loop values (n + 1)
    | [] -> system
  in loop system 0;;

let is_compatible system = 
  let correct_form eq = (match eq with 
    Equality (l, r) -> match l with 
      | Impl _ -> false
      | Var _  -> match r with
        | Impl _ -> true
        | Var _  -> false) in
  let is_correct_eq eq = if correct_form eq 
    then 
      let var = get_eq_var eq in
        let rec walk t = match t with
          | Impl (l, r) -> walk l && walk r
          | Var x       -> x <> var
      in walk (get_eq_right eq)
    else true in 
  let rec loop s = match s with
    | el :: values ->
      if is_correct_eq el then loop values
      else false
    | []           -> true
  in loop system;;

let is_decidability system =
  let correct_form eq = (match eq with
    | Equality (l, r) -> match l with
      | Impl _ -> false
      | Var _  -> true) in
  let rec loop s var_set = match s with
    | el :: values ->
      if correct_form el then
        let cur_var = get_eq_var el in
          if StrSet.mem cur_var var_set then false
          else loop values (StrSet.add cur_var var_set)
      else false
    | [] -> true
  in loop system StrSet.empty;;

let rec solve_system system = 
  let ns = system >> swap_vars >> reduction >> substitution >> remove_equils in
    if is_compatible ns then
      if is_decidability ns then ns else solve_system ns
    else [];;


let input = read_line ();;
let input_tree = input >> Lexing.from_string >> Parser.main Lexer.main;;

let tpair = set_system input_tree;;
print_string "start system:\n";;
print_system tpair;;

let solved_system = tpair >> get_system >> solve_system;;

let solved_pair = TPair(solved_system, get_type tpair);;
print_string "solved system:\n";;
print_system solved_pair;;

let hash_system system = 
  let hash = Hashtbl.create 100 in
    let rec loop s = match s with   
      | el :: values -> (match el with 
        | Equality (l, r) -> 
          let var = get_eq_var el in 
            Hashtbl.add hash var r;
          loop values)
      | [] -> () in
  loop system;
  hash;;

let print_proof system t = 
  let hash_var = Hashtbl.create 100 in
  let hash_sys = hash_system system in
  clr ();

  let get_var_type var = if Hashtbl.mem hash_sys var 
    then Hashtbl.find hash_sys var
    else Var var in

  let rec make_type_list token = (match token with
    | Apply (p, q) -> let lp = make_type_list p in
                        let lq = make_type_list q in
                          let ctp = get_var_type (make_new_var ()) in
                           ctp :: (List.append lp lq)
    | Abstr (v, p) -> let lst = make_type_list p in
                        let pt = List.hd lst in
                          let vt = get_var_type (make_var hash_var v) in 
                            let ct = Impl (vt, pt) in
                              ct :: lst
    | Var v        -> let var = make_var hash_var v in
                        [get_var_type (var)]) in

  let rec add_indent buff i = (if i > 0 then 
    begin
      Buffer.add_string buff "*   ";
      add_indent buff (i - 1);
    end) in

  let rec buff_proof token list buff i = (match list with
      | cur_type :: vls -> (
        add_indent buff i;
        let tree_str = string_of_tree token in 
          let type_str = string_of_type cur_type in
          Buffer.add_string buff (tree_str ^ " : " ^ type_str);
          match token with
            | Var _        -> Buffer.add_string buff " [rule #1]\n";
                              vls
            | Apply (p, q) -> Buffer.add_string buff " [rule #2]\n";
                              let plist = buff_proof p vls buff (i + 1) in
                                buff_proof q plist buff (i + 1)
            | Abstr (_, p) -> Buffer.add_string buff " [rule #3]\n";
                              buff_proof p vls buff (i + 1))
      | [] -> []) in
  let buff = Buffer.create 1000000 in
    buff_proof input_tree (make_type_list input_tree) buff 0;
    Buffer.add_char buff '\n';
    let proof = Buffer.contents buff in
      print_string proof;;

let solve system t = 
  if (List.length system) = 0 then 
    print_string "Expression has no type\n"
  else print_proof system t;;

solve solved_system (get_type tpair);;