open Tree;;
open Buffer;;
open Printf;;
open List;;
open Hashtbl;;

type system_type = 
  | Impl of system_type * system_type
  | Var of string;;

type equation = Equality of system_type * system_type;;
type system = equation list;;

type tpair = TPair of system * system_type;;

let cnt = ref 0;;
let inc () = cnt := !cnt + 1; !cnt;;

let make_var hash var = if Hashtbl.mem hash var then
                          Hashtbl.find hash var 
                        else 
                          let name = "a" ^ (string_of_int (inc ())) in
                            Hashtbl.add hash var name;
                            name;;                  


(* create system block *)

let make_new_var () = "a" ^ (string_of_int (inc ()));;

let get_eq_if b eq = match eq with
  | Equality (l, r) -> if b then r else l;;

let get_eq_left  = get_eq_if false;;
let get_eq_right = get_eq_if true;;

let get_system tpair = match tpair with
  | TPair (system, t) -> system;;

let get_type tpair = match tpair with
  | TPair (system, t) -> t;;

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
  let is_removed_eq eq = match eq with
    | Equality (t1, t2) -> match t1 with
      | Impl _  -> false
      | Var x   -> match t2 with
        | Impl _  -> false
        | Var y   -> if x = y then true else false in
    
        let rec loop s = match s with
          | el :: values  ->  let next = loop values in
                                if is_removed_eq el then next else el :: next
          | []            ->  []
  in loop system;;

let swap_var system = 
  let swap_eq eq = match eq with
    | Equality (t1, t2) -> match t1 with
      | Var x   -> eq
      | Impl _  -> match t2 with
        | Var y   -> Equality (t2, t1)
        | Impl _  -> eq in
    List.map (fun eq -> swap_eq eq) system;;

let reduction system =
  let do_reduction eq = match eq with
    | Equality (t1, t2) -> match t1 with
      | Var x           -> []
      | Impl (t11, t12) -> match t2 with
        | Var y           -> []
        | Impl (t21, t22) -> [Equality (t11, t21); Equality (t12, t22)] in
    let rec loop s = match s with
      | el :: values -> let next = loop values in
                          let new_eq = do_reduction el in
                            if List.length new_eq = 0 
                            then loop values 
                            else new_eq @ next
      | [] -> [];
    in loop system;;


let do_subst system var expr =
  let v = match var with
    | Var variable -> variable
    | Impl _       -> "" in
  let rec loop s = match s with
    | el :: values -> (let next = loop values in match el with
      | Equality (t1, t2) -> match t1 with
        | Impl _ -> el :: next
        | Var x  -> if x = v then
                      (Equality (expr, t2)) :: next 
                    else el :: next)
    | [] -> [] 
  in loop system;;

let substitution system = 
  let is_to_sub eq = match eq with
    | Equality (t1, _) -> match t1 with
      | Impl _ -> false  
      | Var x  -> true in  
  let rec loop s = match s with
    | el :: values -> (if is_to_sub el then 
                        let nv = do_subst values (get_eq_left el) (get_eq_right el) in
                          el :: (loop nv)
                      else el :: (loop values))
    | [] -> []
  in loop system;;

let correct_system system = true;;

let is_over system = false;;

let solve_system system = 
  let rec loop s = 
    let removed_s = remove_equils s in
      let swaped = swap_var removed_s in
        let red_s = reduction swaped in
          let subst = substitution red_s in
            if correct_system subst then
              if is_over subst then subst else loop subst
            else []
  in loop system;;

let (>>) x f = f x;;

let input = read_line ();;
let input_tree = input >> Lexing.from_string >> Parser.main Lexer.main;;

(* input_tree >> set_system >> print_system;; *)