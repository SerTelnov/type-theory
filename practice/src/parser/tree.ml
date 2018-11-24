type tree = 
  | Var of string
  | Abstr of string * tree
  | Apply of tree * tree
  | Nothing;;