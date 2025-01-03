{
  open Lexing
  open Kawaparser 

  exception Error of string

  let keyword_or_ident =
    let h = Hashtbl.create 17 in
    List.iter (fun (s, k) -> Hashtbl.add h s k)
      [ "print", PRINT;
        "main", MAIN;
        "true", TRUE;
        "false", FALSE;
        "var", VAR;
        "attribute", ATTRIBUTE;
        "method", METHOD;
        "class",CLASS;
        "extends",EXTENDS;
        "new",NEW;
        "this",THIS;
        "if",IF;
        "else",ELSE;
        "while",WHILE;
        "return",RETURN;
        "int", TINT;
        "bool",TBOOL;
        "void",TVOID
      ] ;
    fun s ->
      try Hashtbl.find h s
      with Not_found -> IDENT(s)

  let symbol_or_operator =
    let h = Hashtbl.create 17 in
      List.iter (fun (s, k) -> Hashtbl.add h s k) [
        ".", DOT;
        ";", SEMI;
        "(", LPAR;
        ")", RPAR;
        "{", BEGIN;
        "}", END;
        "-", SUB;
        "!", NEG;
        "+", PLUS;
        "=", ASSIGN;
        "*", MUL;
        "/", DIV;
        "%", MOD;
        "==", EQUAL;
        "!=", NEQ;
        "<", LT;
        "<=", LE;
        ">", GT;
        ">=", GE;
        "&&", AND;
        "||", OR;
        ",", COMMA;
    ];
    fun s ->
      try Some (Hashtbl.find h s)
      with Not_found -> None
}


let digit = ['0'-'9']
let number = ['-']? digit+
let alpha = ['a'-'z' 'A'-'Z']
let ident = ['a'-'z' '_'] (alpha | '_' | digit)*
  
rule token = parse
  | ['\n']            { new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r']+  { token lexbuf }

  | "//" [^ '\n']* "\n"  { new_line lexbuf; token lexbuf }
  | "/*"                 { comment lexbuf; token lexbuf }

  | number as n  { 
      if n.[0] = '-' then OPP INT(-int_of_string n) 
      else INT(int_of_string n)
    }

  | ident as id  { keyword_or_ident id }

  | [';' '(' ')' '{' '}' '-' '+' '*' '/' '%' '.'] 
  | ['<' '>' '=' '!'] ['=']?
  | "&&" | "||"
    as sym { match symbol_or_operator sym with 
                Some v -> v
                | _ -> token lexbuf
            }

  | eof  { EOF }
  | _    { raise (Error ("unknown character : " ^ lexeme lexbuf)) }
  

and comment = parse
  | "*/" { () }
  | _    { comment lexbuf }
  | eof  { raise (Error "unterminated comment") }
