open Tree;;
open Buffer;;
open Printf;;
open List;;
open Hashtbl;;

module StrSet = Set.Make(String);;

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


(* create system block *)

let cnt = ref 0;;
let inc () = cnt := !cnt + 1; !cnt;;

let make_var hash var = if Hashtbl.mem hash var then
                          Hashtbl.find hash var 
                        else 
                          let name = "a" ^ (string_of_int (inc ())) in
                            Hashtbl.add hash var name;
                            name;;      

let make_new_var () = "a" ^ (string_of_int (inc ()));;

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


let (>>) x f = f x;;

let input = read_line ();;
let input_tree = input >> Lexing.from_string >> Parser.main Lexer.main;;

let tpair = input_tree >> set_system;;
let solved_system = tpair >> get_system >> solve_system;;