let lex = Lexing.from_channel stdin in
let theory = Parser.theory Lexer.token lex in
  print_endline "Yeah!"
