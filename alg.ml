let lex = Lexing.from_channel stdin in
let raw_theory = Parser.theory Lexer.token lex in
let theory = Cook.cook_theory raw_theory in
  print_endline "Theory was cooked."
