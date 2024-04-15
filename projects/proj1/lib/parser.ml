module AExp = Nice_parser.Make (struct
  type result = Lang.aexp
  type token = Menhir_parser.token

  exception ParseError = Menhir_parser.Error

  let parse = Menhir_parser.aexp_eof

  include Lexer
end)

module BExp = Nice_parser.Make (struct
  type result = Lang.bexp
  type token = Menhir_parser.token

  exception ParseError = Menhir_parser.Error

  let parse = Menhir_parser.bexp_eof

  include Lexer
end)

module Formula = Nice_parser.Make (struct
  type result = Lang.formula
  type token = Menhir_parser.token

  exception ParseError = Menhir_parser.Error

  let parse = Menhir_parser.formula_eof

  include Lexer
end)

module Stmt = Nice_parser.Make (struct
  type result = Lang.stmt
  type token = Menhir_parser.token

  exception ParseError = Menhir_parser.Error

  let parse = Menhir_parser.stmt_eof

  include Lexer
end)

module Meth = Nice_parser.Make (struct
  type result = Lang.meth
  type token = Menhir_parser.token

  exception ParseError = Menhir_parser.Error

  let parse = Menhir_parser.meth_eof

  include Lexer
end)

module Prog = Nice_parser.Make (struct
  type result = Lang.prog
  type token = Menhir_parser.token

  exception ParseError = Menhir_parser.Error

  let parse = Menhir_parser.prog_eof

  include Lexer
end)
