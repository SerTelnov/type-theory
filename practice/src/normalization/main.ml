open Tree;;
open Buffer;;
open Printf;;
open Hashtbl;;

module StringSet = Set.Make(String);;

let string_of_tree tree =
  let buff = Buffer.create 2000000 in
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
  in s_token tree;
  add_char buff '\n';
  contents buff;;

let fill_free_set tree = 
  let rec walk token abstr_set = match token with
    | Apply (p, q) -> StringSet.union (walk p abstr_set) (walk q abstr_set)
    | Abstr (v, t) -> walk t (StringSet.add v abstr_set)
    | Var v        -> if StringSet.mem v abstr_set
                        then StringSet.empty
                        else StringSet.singleton v
  in walk tree (StringSet.empty);;

let fill_set tree = 
  let set = StringSet.empty in
    let rec walk token set = match token with
      | Apply (t1, t2) -> let nset = walk t1 set in 
                            walk t2 nset
      | Abstr (v, t)   -> walk t (StringSet.add v set)
      | Var v          -> StringSet.add v set
  in walk tree set;;

let make_name name new_names =
  let new_name = name ^ (string_of_int (Random.int 100)) in
      Hashtbl.add new_names name new_name;
      new_name;;

let beta_reduction p var q = 
  let q_set = fill_free_set q in
    let new_names = Hashtbl.create 10 in
      let rec walk token change = match token with
        | Abstr (v, t)   -> if v = var then Abstr (v, walk t false)
                            else if StringSet.mem v q_set then
                              let name = make_name v new_names in
                                  let ntoken = Abstr (name, walk t change) in
                                    Hashtbl.remove new_names v;
                                    ntoken;
                            else Abstr (v, walk t change)
        | Apply (t1, t2) -> Apply (walk t1 change, walk t2 change)
        | Var v          -> if Hashtbl.mem new_names v then
                              Var (Hashtbl.find new_names v)
                            else if v = var && change then q
                            else token
      in walk p true;;

let do_reduction tree =
  let rec walk token = match token with
    | Abstr (v, p) -> Abstr (v, walk p)
    | Var v        -> token
    | Apply (p, q) -> match p with
      | Abstr (v, r) -> beta_reduction r v q
      | Apply (r, t) -> Apply (walk p, walk q)
      | Var v        -> Apply (p, walk q)
  in walk tree;;

let rec has_redex tree = match tree with
  | Abstr (v, p) -> has_redex p
  | Var v        -> false
  | Apply (p, q) -> match p with 
    | Abstr(_, _) -> true
    | Apply(_, _) -> has_redex p || has_redex q
    | Var _       -> has_redex q;;
    
    
let (>>) x f = f x;;

let rec normalization tree = if has_redex tree
  then normalization (do_reduction tree)
  else tree;;

let input = read_line ();;


let input_tree = input >> Lexing.from_string >> Parser.main Lexer.main;;

input_tree >> normalization >> string_of_tree >> print_string;;