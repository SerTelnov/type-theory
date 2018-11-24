{
  open Parser;;
}

let variable_regex   = ['a'-'z'] (['a'-'z']|['0'-'9']|''')*
let whitespace_regex = (' '|'\n'|'\r'|'\t')+

rule main = parse
  | whitespace_regex    { main lexbuf }
  | variable_regex as v { VAR (v) }
  | "\\"                { LAMBDA }
  | "."                 { DOT }
  | "("                 { OPEN }
  | ")"                 { CLOSE }
  | eof                 { EOF }