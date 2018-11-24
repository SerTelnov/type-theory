%{
  open Tree;;
%}
%token <string> VAR
%token OPEN CLOSE
%token DOT LAMBDA
%token EOF
%start main
%type <Tree.tree> main
%%

main:
        | expr EOF                        { $1 }
        | EOF                             { Nothing }

expr:
        | apply                         { $1 }
        | apply LAMBDA VAR DOT expr     { Apply ($1, Abstr($3, $5)) }
        | LAMBDA VAR DOT expr           { Abstr ($2, $4) }
        
apply:
        | apply variable                { Apply ($1, $2) }
        | variable                      { $1 }

variable:
        | OPEN expr CLOSE               { $2 }
        | VAR                           { Var $1 }