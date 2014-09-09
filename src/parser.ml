exception Error

type token = 
  | UNARY
  | TRUE
  | THEORY
  | THEOREM
  | RPAREN
  | RELATION
  | PREFIXOP of (string)
  | PREDICATE
  | OR
  | NOTEQUAL
  | NOT
  | LPAREN
  | INFIXOP4 of (string)
  | INFIXOP3 of (string)
  | INFIXOP2 of (string)
  | INFIXOP1 of (string)
  | INFIXOP0 of (string)
  | IMPLY
  | IFF
  | IDENT of (string)
  | FORALL
  | FALSE
  | EXISTS
  | EQUAL
  | EOF
  | DOT
  | CONSTANT
  | COMMA
  | COLON
  | BINARY
  | AXIOM
  | AND

and _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  mutable _menhir_token: token;
  mutable _menhir_startp: Lexing.position;
  mutable _menhir_endp: Lexing.position;
  mutable _menhir_shifted: int
}

and _menhir_state = 
  | MenhirState222
  | MenhirState219
  | MenhirState217
  | MenhirState215
  | MenhirState213
  | MenhirState211
  | MenhirState208
  | MenhirState201
  | MenhirState193
  | MenhirState185
  | MenhirState179
  | MenhirState173
  | MenhirState166
  | MenhirState156
  | MenhirState154
  | MenhirState153
  | MenhirState151
  | MenhirState150
  | MenhirState149
  | MenhirState146
  | MenhirState143
  | MenhirState140
  | MenhirState139
  | MenhirState127
  | MenhirState122
  | MenhirState120
  | MenhirState116
  | MenhirState115
  | MenhirState106
  | MenhirState100
  | MenhirState91
  | MenhirState83
  | MenhirState81
  | MenhirState80
  | MenhirState75
  | MenhirState59
  | MenhirState57
  | MenhirState55
  | MenhirState53
  | MenhirState51
  | MenhirState49
  | MenhirState47
  | MenhirState45
  | MenhirState43
  | MenhirState41
  | MenhirState39
  | MenhirState38
  | MenhirState24
  | MenhirState22
  | MenhirState20
  | MenhirState18
  | MenhirState16
  | MenhirState11
  | MenhirState9
  | MenhirState8
  | MenhirState4
  | MenhirState3
  | MenhirState2
  | MenhirState0

  
let _eRR =
  Error

let rec _menhir_reduce70 : _menhir_env -> 'ttv_tail * _menhir_state * Lexing.position -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _ f _endpos_f_ ->
    let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( Input.Not f ) in
    _menhir_goto_plain_negation_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce46 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _ f2 _endpos_f2_ ->
    let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
    let _startpos = _startpos_f1_ in
    let _endpos = _endpos_f2_ in
    let _v : (Input.formula') =     ( Input.And (f1, f2) ) in
    _menhir_goto_plain_and_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce75 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _ f2 _endpos_f2_ ->
    let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
    let _startpos = _startpos_f1_ in
    let _endpos = _endpos_f2_ in
    let _v : (Input.formula') =     ( Input.Or (f1, f2) ) in
    _menhir_goto_plain_or_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce67 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _ f2 _endpos_f2_ ->
    let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
    let _startpos = _startpos_f1_ in
    let _endpos = _endpos_f2_ in
    let _v : (Input.formula') =     ( Input.Imply (f1, f2) ) in
    _menhir_goto_plain_imply_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce105 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _1 _endpos__1_ ->
    let _endpos = _endpos__1_ in
    let _v : (Input.formula) =                                                             ( _1 ) in
    match _menhir_s with
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce75 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce46 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce70 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce75 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState173 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce46 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce70 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce5 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _1 _endpos__1_ ->
    let _endpos = _endpos__1_ in
    let _v : (Input.formula) =                                       ( _1 ) in
    match _menhir_s with
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce67 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _1 = _v in
        let _endpos__1_ = _endpos in
        Obj.magic _1
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce67 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState149 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let a = _v in
        let _endpos_a_ = _endpos in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _, n) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_a_ in
        let _v : (Input.theory_entry') =     ( Input.Axiom (n, a) ) in
        _menhir_goto_plain_theory_entry _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState219 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let a = _v in
        let _endpos_a_ = _endpos in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _, n) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_a_ in
        let _v : (Input.theory_entry') =     ( Input.Axiom (n, a) ) in
        _menhir_goto_plain_theory_entry _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce59 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s f _startpos_f_ _endpos_f_ ->
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce18 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s x _startpos_x_ _endpos_x_ ->
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.formula) =   ( x, Common.Position (_startpos, _endpos) ) in
    match _menhir_s with
    | MenhirState38 | MenhirState91 | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce105 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState150 | MenhirState173 | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce105 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce62 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s f _startpos_f_ _endpos_f_ ->
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce12 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s x _startpos_x_ _endpos_x_ ->
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.formula) =   ( x, Common.Position (_startpos, _endpos) ) in
    match _menhir_s with
    | MenhirState0 | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce5 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState219 | MenhirState149 | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce5 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_quantified_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState41 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce62 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState38 | MenhirState91 | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce18 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState0 | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce59 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState153 | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce62 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState150 | MenhirState173 | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce18 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState219 | MenhirState149 | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce59 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce60 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s f _startpos_f_ _endpos_f_ ->
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_goto_plain_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState0 | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce12 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState219 | MenhirState149 | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce12 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce81 : _menhir_env -> ('ttv_tail * _menhir_state * Lexing.position) * _menhir_state * (Input.variable list) -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _ f _endpos_f_ ->
    let ((_menhir_stack, _menhir_s, _startpos__1_), _, xs) = _menhir_stack in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( Input.Forall (xs, f) ) in
    _menhir_goto_plain_quantified_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce82 : _menhir_env -> ('ttv_tail * _menhir_state * Lexing.position) * _menhir_state * (Input.variable list) -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _ f _endpos_f_ ->
    let ((_menhir_stack, _menhir_s, _startpos__1_), _, xs) = _menhir_stack in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( Input.Exists (xs, f) ) in
    _menhir_goto_plain_quantified_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce65 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _ f2 _endpos_f2_ ->
    let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
    let _startpos = _startpos_f1_ in
    let _endpos = _endpos_f2_ in
    let _v : (Input.formula') =     ( Input.Iff (f1, f2) ) in
    match _menhir_s with
    | MenhirState0 | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce60 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState219 | MenhirState149 | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce60 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce61 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s f _startpos_f_ _endpos_f_ ->
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce63 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s f _startpos_f_ _endpos_f_ ->
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce6 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _1 _endpos__1_ ->
    let _endpos = _endpos__1_ in
    let _v : (Input.formula) =                                                       ( _1 ) in
    match _menhir_s with
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce82 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState41 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce81 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce82 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState153 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce81 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce43 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _1 _endpos__1_ ->
    let _endpos = _endpos__1_ in
    let _v : (Input.formula) =                                             ( _1 ) in
    match _menhir_s with
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce65 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce65 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_imply_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState41 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce63 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState0 | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce61 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState153 | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce63 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState219 | MenhirState149 | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce61 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce13 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s x _startpos_x_ _endpos_x_ ->
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.formula) =   ( x, Common.Position (_startpos, _endpos) ) in
    match _menhir_s with
    | MenhirState41 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState153 | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_relation : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let f = _v in
    let _startpos_f_ = _startpos in
    let _endpos_f_ = _endpos in
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_atomic_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce51 : _menhir_env -> (((('ttv_tail * _menhir_state * (Input.operation) * Lexing.position * Lexing.position) * _menhir_state * Lexing.position) * _menhir_state * (Input.term) * Lexing.position * Lexing.position) * _menhir_state * (Input.term) * Lexing.position * Lexing.position) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((((_menhir_stack, _menhir_s, op, _startpos_op_, _endpos_op_), _, _startpos__2_), _, t1, _startpos_t1_, _endpos_t1_), _, t2, _startpos_t2_, _endpos_t2_), _endpos__6_) = _menhir_stack in
    let _startpos = _startpos_op_ in
    let _endpos = _endpos__6_ in
    let _v : (Input.term') =     ( Input.BinaryOp (op, t1, t2) ) in
    _menhir_goto_plain_app_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce91 : _menhir_env -> (('ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position) * (string) * Lexing.position) * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), op0, _endpos_op0_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
    let _startpos = _startpos_t1_ in
    let _endpos = _endpos_t2_ in
    let _v : (Input.term') = let op =
      let op = op0 in
          ( op )
    in
        ( Input.BinaryOp (op, t1, t2) ) in
    _menhir_goto_plain_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce92 : _menhir_env -> (('ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position) * (string) * Lexing.position) * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), op0, _endpos_op0_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
    let _startpos = _startpos_t1_ in
    let _endpos = _endpos_t2_ in
    let _v : (Input.term') = let op =
      let op = op0 in
          ( op )
    in
        ( Input.BinaryOp (op, t1, t2) ) in
    _menhir_goto_plain_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce93 : _menhir_env -> (('ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position) * (string) * Lexing.position) * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), op0, _endpos_op0_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
    let _startpos = _startpos_t1_ in
    let _endpos = _endpos_t2_ in
    let _v : (Input.term') = let op =
      let op = op0 in
          ( op )
    in
        ( Input.BinaryOp (op, t1, t2) ) in
    _menhir_goto_plain_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce94 : _menhir_env -> (('ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position) * (string) * Lexing.position) * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), op0, _endpos_op0_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
    let _startpos = _startpos_t1_ in
    let _endpos = _endpos_t2_ in
    let _v : (Input.term') = let op =
      let op = op0 in
          ( op )
    in
        ( Input.BinaryOp (op, t1, t2) ) in
    _menhir_goto_plain_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce95 : _menhir_env -> (('ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position) * (string) * Lexing.position) * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), op0, _endpos_op0_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
    let _startpos = _startpos_t1_ in
    let _endpos = _endpos_t2_ in
    let _v : (Input.term') = let op =
      let op = op0 in
          ( op )
    in
        ( Input.BinaryOp (op, t1, t2) ) in
    _menhir_goto_plain_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_run11 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _v _endpos ->
    let _menhir_stack = (_menhir_stack, _v, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState11

and _menhir_run16 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _v _endpos ->
    let _menhir_stack = (_menhir_stack, _v, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16

and _menhir_run18 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _v _endpos ->
    let _menhir_stack = (_menhir_stack, _v, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18

and _menhir_run20 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _v _endpos ->
    let _menhir_stack = (_menhir_stack, _v, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20

and _menhir_run22 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _v _endpos ->
    let _menhir_stack = (_menhir_stack, _v, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState22

and _menhir_reduce74 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _ f2 _endpos_f2_ ->
    let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
    let _startpos = _startpos_f1_ in
    let _endpos = _endpos_f2_ in
    let _v : (Input.formula') =     ( Input.Or (f1, f2) ) in
    _menhir_goto_plain_or_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce16 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s x _startpos_x_ _endpos_x_ ->
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.formula) =   ( x, Common.Position (_startpos, _endpos) ) in
    match _menhir_s with
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce43 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce43 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce68 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s f _startpos_f_ _endpos_f_ ->
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_imply_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_goto_plain_formula_noquant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState41 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce13 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState153 | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce13 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce20 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term') * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, x, _startpos_x_, _endpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.term) =   ( x, Common.Position (_startpos, _endpos) ) in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _startpos__1_ = _startpos in
    let _endpos__1_ = _endpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Input.term) =                                 ( _1 ) in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24)
        | INFIXOP0 _v ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce95 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce94 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce93 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce92 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce91 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP0 _v ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _ = _menhir_discard _menhir_env in
            _menhir_reduce51 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP0 _v ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState219 | MenhirState149 | MenhirState150 | MenhirState153 | MenhirState193 | MenhirState185 | MenhirState179 | MenhirState173 | MenhirState166 | MenhirState156 | MenhirState0 | MenhirState38 | MenhirState41 | MenhirState122 | MenhirState120 | MenhirState115 | MenhirState116 | MenhirState106 | MenhirState100 | MenhirState91 | MenhirState75 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59)
        | INFIXOP0 _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState57)
        | INFIXOP1 _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55)
        | INFIXOP2 _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState53 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState53 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState53 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState53)
        | INFIXOP3 _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState51 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState51 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState51 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState51)
        | INFIXOP4 _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49)
        | NOTEQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP0 _v ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | DOT | IFF | IMPLY | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
            let _startpos = _startpos_t1_ in
            let _endpos = _endpos_t2_ in
            let _v : (Input.formula') =     ( Input.NotEqual (t1, t2) ) in
            _menhir_goto_plain_atomic_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState49 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | NOTEQUAL ->
            _menhir_reduce95 _menhir_env (Obj.magic _menhir_stack)
        | AND | DOT | IFF | IMPLY | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), op0, _endpos_op0_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
            let _startpos = _startpos_t1_ in
            let _endpos = _endpos_t2_ in
            let _v : (Input.formula') = let op =
              let op = op0 in
                  ( op )
            in
                ( Input.BinaryPr (op, t1, t2) ) in
            _menhir_goto_plain_relation _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | NOTEQUAL ->
            _menhir_reduce94 _menhir_env (Obj.magic _menhir_stack)
        | AND | DOT | IFF | IMPLY | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), op0, _endpos_op0_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
            let _startpos = _startpos_t1_ in
            let _endpos = _endpos_t2_ in
            let _v : (Input.formula') = let op =
              let op = op0 in
                  ( op )
            in
                ( Input.BinaryPr (op, t1, t2) ) in
            _menhir_goto_plain_relation _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState53 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | NOTEQUAL ->
            _menhir_reduce93 _menhir_env (Obj.magic _menhir_stack)
        | AND | DOT | IFF | IMPLY | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), op0, _endpos_op0_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
            let _startpos = _startpos_t1_ in
            let _endpos = _endpos_t2_ in
            let _v : (Input.formula') = let op =
              let op = op0 in
                  ( op )
            in
                ( Input.BinaryPr (op, t1, t2) ) in
            _menhir_goto_plain_relation _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | EQUAL | INFIXOP0 _ | NOTEQUAL ->
            _menhir_reduce92 _menhir_env (Obj.magic _menhir_stack)
        | AND | DOT | IFF | IMPLY | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), op0, _endpos_op0_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
            let _startpos = _startpos_t1_ in
            let _endpos = _endpos_t2_ in
            let _v : (Input.formula') = let op =
              let op = op0 in
                  ( op )
            in
                ( Input.BinaryPr (op, t1, t2) ) in
            _menhir_goto_plain_relation _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | EQUAL | INFIXOP0 _ | NOTEQUAL ->
            _menhir_reduce91 _menhir_env (Obj.magic _menhir_stack)
        | AND | DOT | IFF | IMPLY | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), op0, _endpos_op0_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
            let _startpos = _startpos_t1_ in
            let _endpos = _endpos_t2_ in
            let _v : (Input.formula') = let op =
              let op = op0 in
                  ( op )
            in
                ( Input.BinaryPr (op, t1, t2) ) in
            _menhir_goto_plain_relation _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP0 _v ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | DOT | IFF | IMPLY | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, t1, _startpos_t1_, _endpos_t1_), _, t2, _startpos_t2_, _endpos_t2_) = _menhir_stack in
            let _startpos = _startpos_t1_ in
            let _endpos = _endpos_t2_ in
            let _v : (Input.formula') =     ( Input.Equal (t1, t2) ) in
            _menhir_goto_plain_atomic_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState83)
        | INFIXOP0 _v ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP0 _v ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | AND | DOT | IFF | IMPLY | OR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((((_menhir_stack, _menhir_s, op, _startpos_op_, _endpos_op_), _, _startpos__2_), _, t1, _startpos_t1_, _endpos_t1_), _, t2, _startpos_t2_, _endpos_t2_), _endpos__6_) = _menhir_stack in
                let _startpos = _startpos_op_ in
                let _endpos = _endpos__6_ in
                let _v : (Input.formula') =     ( Input.BinaryPr (op, t1, t2) ) in
                _menhir_goto_plain_relation _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
            | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | INFIXOP4 _ | NOTEQUAL ->
                _menhir_reduce51 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _, _, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce2 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _1 _endpos__1_ ->
    let _endpos = _endpos__1_ in
    let _v : (Input.formula) =                                               ( _1 ) in
    match _menhir_s with
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce74 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce74 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_or_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState0 | MenhirState41 | MenhirState100 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce68 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce16 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState219 | MenhirState149 | MenhirState153 | MenhirState179 | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce68 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce16 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_run173 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState173 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState173

and _menhir_run122 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122

and _menhir_reduce77 : _menhir_env -> ('ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position) * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_), _, f2, _startpos_f2_, _endpos_f2_) = _menhir_stack in
    let _startpos = _startpos_f1_ in
    let _endpos = _endpos_f2_ in
    let _v : (Input.formula') =     ( Input.Or (f1, f2) ) in
    _menhir_goto_plain_or_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_run91 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91

and _menhir_reduce64 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s f _startpos_f_ _endpos_f_ ->
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_run166 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState166

and _menhir_run179 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState179

and _menhir_run120 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState120

and _menhir_run75 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75

and _menhir_run100 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100

and _menhir_run116 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116

and _menhir_goto_plain_term : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.term') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState219 | MenhirState149 | MenhirState150 | MenhirState153 | MenhirState193 | MenhirState185 | MenhirState179 | MenhirState173 | MenhirState166 | MenhirState156 | MenhirState0 | MenhirState38 | MenhirState41 | MenhirState122 | MenhirState120 | MenhirState115 | MenhirState116 | MenhirState106 | MenhirState100 | MenhirState91 | MenhirState83 | MenhirState75 | MenhirState45 | MenhirState59 | MenhirState57 | MenhirState55 | MenhirState53 | MenhirState51 | MenhirState49 | MenhirState47 | MenhirState24 | MenhirState22 | MenhirState20 | MenhirState18 | MenhirState16 | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce20 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState81 | MenhirState3 | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _ = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos__3_ = _endpos in
            let ((_menhir_stack, _menhir_s, _startpos__1_), _, t, _startpos_t_, _endpos_t_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos__3_ in
            let _v : (Input.term') =     ( t ) in
            _menhir_goto_plain_simple_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | COMMA | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | INFIXOP4 _ ->
            _menhir_reduce20 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce69 : _menhir_env -> 'ttv_tail * _menhir_state * Lexing.position -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _ f _endpos_f_ ->
    let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( Input.Not f ) in
    _menhir_goto_plain_negation_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce45 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _ f2 _endpos_f2_ ->
    let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
    let _startpos = _startpos_f1_ in
    let _endpos = _endpos_f2_ in
    let _v : (Input.formula') =     ( Input.And (f1, f2) ) in
    _menhir_goto_plain_and_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce9 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s x _startpos_x_ _endpos_x_ ->
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.formula) =   ( x, Common.Position (_startpos, _endpos) ) in
    match _menhir_s with
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce2 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce2 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce76 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s f _startpos_f_ _endpos_f_ ->
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_or_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce10 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula') * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, x, _startpos_x_, _endpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.formula) =   ( x, Common.Position (_startpos, _endpos) ) in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _startpos__1_ = _startpos in
    let _endpos__1_ = _endpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Input.formula) =                                                               ( _1 ) in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack)
        | IFF | IMPLY | OR ->
            _menhir_reduce77 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 | MenhirState41 | MenhirState45 | MenhirState100 | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | DOT | OR ->
            _menhir_reduce77 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState193 | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | IFF | IMPLY | OR ->
            _menhir_reduce77 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState219 | MenhirState149 | MenhirState153 | MenhirState156 | MenhirState179 | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run173 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_or_formula_noquant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let x = _v in
    let _startpos_x_ = _startpos in
    let _endpos_x_ = _endpos in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.formula) =   ( x, Common.Position (_startpos, _endpos) ) in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _startpos__1_ = _startpos in
    let _endpos__1_ = _endpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Input.formula) =                                                             ( _1 ) in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState41 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IFF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState115)
        | IMPLY ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IFF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState106)
        | IMPLY ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OR ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OR ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState153 | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IFF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState193)
        | IMPLY ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState219 | MenhirState149 | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IFF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState185)
        | IMPLY ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OR ->
            _menhir_run166 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState193 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OR ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack)
        | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_), _, f2, _startpos_f2_, _endpos_f2_) = _menhir_stack in
            let _startpos = _startpos_f1_ in
            let _endpos = _endpos_f2_ in
            let _v : (Input.formula') =     ( Input.Iff (f1, f2) ) in
            (match _menhir_s with
            | MenhirState41 | MenhirState45 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                _menhir_reduce64 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
            | MenhirState153 | MenhirState156 ->
                let _menhir_stack = Obj.magic _menhir_stack in
                _menhir_reduce64 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
            | _ ->
                _menhir_fail ())
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_predicate : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let f = _v in
    let _startpos_f_ = _startpos in
    let _endpos_f_ = _endpos in
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_atomic_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce50 : _menhir_env -> ('ttv_tail * _menhir_state * (Input.operation) * Lexing.position * Lexing.position) * _menhir_state * (Input.term) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((_menhir_stack, _menhir_s, op, _startpos_op_, _endpos_op_), _, t, _endpos_t_) = _menhir_stack in
    let _startpos = _startpos_op_ in
    let _endpos = _endpos_t_ in
    let _v : (Input.term') =     ( Input.UnaryOp (op, t) ) in
    _menhir_goto_plain_app_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_goto_plain_app_term : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.term') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState2 | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let x = _v in
        let _startpos_x_ = _startpos in
        let _endpos_x_ = _endpos in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : (Input.term) =   ( x, Common.Position (_startpos, _endpos) ) in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _1 = _v in
        let _endpos__1_ = _endpos in
        let _endpos = _endpos__1_ in
        let _v : (Input.term) =                                         ( _1 ) in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let t = _v in
        let _endpos_t_ = _endpos in
        let (_menhir_stack, _menhir_s, op, _startpos_op_, _endpos_op_) = _menhir_stack in
        let _startpos = _startpos_op_ in
        let _endpos = _endpos_t_ in
        let _v : (Input.term') =     ( Input.UnaryOp (op, t) ) in
        _menhir_goto_plain_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState219 | MenhirState149 | MenhirState150 | MenhirState153 | MenhirState193 | MenhirState185 | MenhirState179 | MenhirState173 | MenhirState166 | MenhirState156 | MenhirState0 | MenhirState38 | MenhirState41 | MenhirState122 | MenhirState120 | MenhirState115 | MenhirState116 | MenhirState106 | MenhirState100 | MenhirState91 | MenhirState81 | MenhirState83 | MenhirState75 | MenhirState45 | MenhirState59 | MenhirState57 | MenhirState55 | MenhirState53 | MenhirState51 | MenhirState49 | MenhirState47 | MenhirState3 | MenhirState9 | MenhirState24 | MenhirState22 | MenhirState20 | MenhirState18 | MenhirState16 | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let t = _v in
        let _startpos_t_ = _startpos in
        let _endpos_t_ = _endpos in
        let _startpos = _startpos_t_ in
        let _endpos = _endpos_t_ in
        let _v : (Input.term') =     ( t ) in
        _menhir_goto_plain_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce31 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _1 _endpos__1_ ->
    let _endpos = _endpos__1_ in
    let _v : (Input.formula) =                                                         ( _1 ) in
    match _menhir_s with
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce45 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce69 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState173 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce45 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce69 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_and_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState0 | MenhirState41 | MenhirState106 | MenhirState100 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce76 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState219 | MenhirState149 | MenhirState153 | MenhirState185 | MenhirState179 | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce76 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_and_formula_noquant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState219 | MenhirState149 | MenhirState153 | MenhirState193 | MenhirState185 | MenhirState179 | MenhirState156 | MenhirState0 | MenhirState41 | MenhirState115 | MenhirState106 | MenhirState100 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT | IFF | IMPLY | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, f, _startpos_f_, _endpos_f_) = _menhir_stack in
            let _startpos = _startpos_f_ in
            let _endpos = _endpos_f_ in
            let _v : (Input.formula') =     ( f ) in
            _menhir_goto_plain_or_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | AND ->
            _menhir_reduce10 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState166 | MenhirState120 | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce10 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_reduce19 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term') * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, x, _startpos_x_, _endpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.term) =   ( x, Common.Position (_startpos, _endpos) ) in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _endpos__1_ = _endpos in
    let _endpos = _endpos__1_ in
    let _v : (Input.term) =                                               ( _1 ) in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _endpos) in
    match _menhir_s with
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce50 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, op, _startpos_op_, _endpos_op_), _, t, _endpos_t_) = _menhir_stack in
        let _startpos = _startpos_op_ in
        let _endpos = _endpos_t_ in
        let _v : (Input.formula') =     ( Input.UnaryPr (op, t) ) in
        _menhir_goto_plain_predicate _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND | DOT | IFF | IMPLY | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, op, _startpos_op_, _endpos_op_), _, t, _endpos_t_) = _menhir_stack in
            let _startpos = _startpos_op_ in
            let _endpos = _endpos_t_ in
            let _v : (Input.formula') =     ( Input.UnaryPr (op, t) ) in
            _menhir_goto_plain_predicate _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | INFIXOP4 _ | NOTEQUAL ->
            _menhir_reduce50 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce52 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term') * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, t, _startpos_t_, _endpos_t_) = _menhir_stack in
    let _startpos = _startpos_t_ in
    let _endpos = _endpos_t_ in
    let _v : (Input.term') =     ( t ) in
    _menhir_goto_plain_app_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce14 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s x _startpos_x_ _endpos_x_ ->
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.formula) =   ( x, Common.Position (_startpos, _endpos) ) in
    match _menhir_s with
    | MenhirState38 | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce31 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | MenhirState150 | MenhirState173 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce31 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce47 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s f _startpos_f_ _endpos_f_ ->
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_and_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_goto_plain_negation_formula_noquant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState219 | MenhirState149 | MenhirState153 | MenhirState193 | MenhirState185 | MenhirState179 | MenhirState166 | MenhirState156 | MenhirState0 | MenhirState41 | MenhirState120 | MenhirState115 | MenhirState106 | MenhirState100 | MenhirState75 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _startpos_f_ = _startpos in
        let _endpos_f_ = _endpos in
        let _startpos = _startpos_f_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( f ) in
        _menhir_goto_plain_and_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState150 | MenhirState173 | MenhirState38 | MenhirState122 | MenhirState116 | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let x = _v in
        let _startpos_x_ = _startpos in
        let _endpos_x_ = _endpos in
        let _startpos = _startpos_x_ in
        let _endpos = _endpos_x_ in
        let _v : (Input.formula) =   ( x, Common.Position (_startpos, _endpos) ) in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _1 = _v in
        let _endpos__1_ = _endpos in
        let _endpos = _endpos__1_ in
        let _v : (Input.formula) =                                                                         ( _1 ) in
        (match _menhir_s with
        | MenhirState173 | MenhirState122 | MenhirState91 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let f2 = _v in
            let _endpos_f2_ = _endpos in
            let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
            let _startpos = _startpos_f1_ in
            let _endpos = _endpos_f2_ in
            let _v : (Input.formula') =     ( Input.And (f1, f2) ) in
            _menhir_goto_plain_and_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | MenhirState150 | MenhirState38 | MenhirState116 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let f = _v in
            let _endpos_f_ = _endpos in
            let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_f_ in
            let _v : (Input.formula') =     ( Input.Not f ) in
            _menhir_goto_plain_negation_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            _menhir_fail ())
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_IDENT_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (string option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | EXISTS ->
                _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _menhir_env._menhir_startp
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | FORALL ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _menhir_env._menhir_startp
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState149)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState217 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | EXISTS ->
                _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _menhir_env._menhir_startp
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | FORALL ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _menhir_env._menhir_startp
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState219)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_name_or_op_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.operation list) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    match _menhir_s with
    | MenhirState201 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let lst = _v in
        let _endpos_lst_ = _endpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_lst_ in
        let _v : (Input.theory_entry') =     ( Input.Relation lst ) in
        _menhir_goto_plain_theory_entry _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let xs = _v in
        let _endpos_xs_ = _endpos in
        let (_menhir_stack, _menhir_s, x, _endpos_x_) = _menhir_stack in
        let _endpos = _endpos_xs_ in
        let _v : (Input.operation list) =     ( x :: xs ) in
        _menhir_goto_nonempty_list_name_or_op_ _menhir_env _menhir_stack _menhir_s _v _endpos
    | MenhirState215 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let lst = _v in
        let _endpos_lst_ = _endpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_lst_ in
        let _v : (Input.theory_entry') =     ( Input.Binary lst ) in
        _menhir_goto_plain_theory_entry _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_name_or_prefix_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.operation list) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    match _menhir_s with
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let lst = _v in
        let _endpos_lst_ = _endpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_lst_ in
        let _v : (Input.theory_entry') =     ( Input.Unary lst ) in
        _menhir_goto_plain_theory_entry _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let xs = _v in
        let _endpos_xs_ = _endpos in
        let (_menhir_stack, _menhir_s, x, _endpos_x_) = _menhir_stack in
        let _endpos = _endpos_xs_ in
        let _v : (Input.operation list) =     ( x :: xs ) in
        _menhir_goto_nonempty_list_name_or_prefix_ _menhir_env _menhir_stack _menhir_s _v _endpos
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let lst = _v in
        let _endpos_lst_ = _endpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_lst_ in
        let _v : (Input.theory_entry') =     ( Input.Predicate lst ) in
        _menhir_goto_plain_theory_entry _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_theory_entry : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.theory_entry') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let x = _v in
    let _startpos_x_ = _startpos in
    let _endpos_x_ = _endpos in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.theory_entry) =   ( x, Common.Position (_startpos, _endpos) ) in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = _v in
    let _v : (Input.theory_entry) =                                                 ( _1 ) in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | AXIOM ->
            _menhir_run217 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _menhir_env._menhir_startp
        | BINARY ->
            _menhir_run215 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _menhir_env._menhir_startp
        | CONSTANT ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _menhir_env._menhir_startp
        | PREDICATE ->
            _menhir_run211 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _menhir_env._menhir_startp
        | RELATION ->
            _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _menhir_env._menhir_startp
        | THEOREM ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _menhir_env._menhir_startp
        | UNARY ->
            _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState222 _menhir_env._menhir_startp
        | EOF ->
            _menhir_reduce7 _menhir_env (Obj.magic _menhir_stack) MenhirState222
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState222)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run150 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState150

and _menhir_run151 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState151

and _menhir_run154 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState154

and _menhir_goto_plain_simple_term : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.term') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState219 | MenhirState149 | MenhirState150 | MenhirState153 | MenhirState193 | MenhirState185 | MenhirState179 | MenhirState173 | MenhirState166 | MenhirState156 | MenhirState0 | MenhirState38 | MenhirState41 | MenhirState122 | MenhirState120 | MenhirState115 | MenhirState116 | MenhirState106 | MenhirState100 | MenhirState91 | MenhirState81 | MenhirState83 | MenhirState75 | MenhirState45 | MenhirState59 | MenhirState57 | MenhirState55 | MenhirState53 | MenhirState51 | MenhirState49 | MenhirState47 | MenhirState3 | MenhirState9 | MenhirState24 | MenhirState22 | MenhirState20 | MenhirState18 | MenhirState16 | MenhirState11 | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce52 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState80 | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce19 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | INFIXOP4 _ | NOTEQUAL ->
            _menhir_reduce52 _menhir_env (Obj.magic _menhir_stack)
        | AND | DOT | IFF | IMPLY | OR ->
            _menhir_reduce19 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_negation_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState0 | MenhirState41 | MenhirState106 | MenhirState100 | MenhirState75 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce47 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState38 | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce14 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState219 | MenhirState149 | MenhirState153 | MenhirState185 | MenhirState179 | MenhirState166 | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce47 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | MenhirState150 | MenhirState173 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce14 _menhir_env (Obj.magic _menhir_stack) _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce73 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula') * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, f, _startpos_f_, _endpos_f_) = _menhir_stack in
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_negation_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_goto_list_terminated_theory_entry_DOT__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.theory_entry list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, x0), _, xs) = _menhir_stack in
        let _v : (Input.theory_entry list) = let x =
          let x = x0 in
              ( x )
        in
            ( x :: xs ) in
        _menhir_goto_list_terminated_theory_entry_DOT__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, n), _, lst) = _menhir_stack in
            let _v : (Input.theory) =   ( {Input.th_name = n; Input.th_entries = lst} ) in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _1 = _v in
            Obj.magic _1
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run141 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let op = _v in
    let _startpos_op_ = _startpos in
    let _endpos_op_ = _endpos in
    let _endpos = _endpos_op_ in
    let _v : (Input.operation) =     ( op ) in
    _menhir_goto_name_or_prefix _menhir_env _menhir_stack _menhir_s _v _endpos

and _menhir_run202 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let op0 = _v in
    let _endpos_op0_ = _endpos in
    let _endpos = _endpos_op0_ in
    let _v : (Input.operation) = let op =
      let op = op0 in
          ( op )
    in
        ( op ) in
    _menhir_goto_name_or_op _menhir_env _menhir_stack _menhir_s _v _endpos

and _menhir_run203 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let op0 = _v in
    let _endpos_op0_ = _endpos in
    let _endpos = _endpos_op0_ in
    let _v : (Input.operation) = let op =
      let op = op0 in
          ( op )
    in
        ( op ) in
    _menhir_goto_name_or_op _menhir_env _menhir_stack _menhir_s _v _endpos

and _menhir_run204 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let op0 = _v in
    let _endpos_op0_ = _endpos in
    let _endpos = _endpos_op0_ in
    let _v : (Input.operation) = let op =
      let op = op0 in
          ( op )
    in
        ( op ) in
    _menhir_goto_name_or_op _menhir_env _menhir_stack _menhir_s _v _endpos

and _menhir_run205 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let op0 = _v in
    let _endpos_op0_ = _endpos in
    let _endpos = _endpos_op0_ in
    let _v : (Input.operation) = let op =
      let op = op0 in
          ( op )
    in
        ( op ) in
    _menhir_goto_name_or_op _menhir_env _menhir_stack _menhir_s _v _endpos

and _menhir_run206 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let op0 = _v in
    let _endpos_op0_ = _endpos in
    let _endpos = _endpos_op0_ in
    let _v : (Input.operation) = let op =
      let op = op0 in
          ( op )
    in
        ( op ) in
    _menhir_goto_name_or_op _menhir_env _menhir_stack _menhir_s _v _endpos

and _menhir_reduce39 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (string option) =     ( None ) in
    _menhir_goto_option_IDENT_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run147 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let x = _v in
    let _startpos_x_ = _startpos in
    let _endpos_x_ = _endpos in
    let _v : (string option) =     ( Some x ) in
    _menhir_goto_option_IDENT_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_name_or_op : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.operation) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _endpos) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | INFIXOP0 _v ->
        _menhir_run206 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v _menhir_env._menhir_endp
    | INFIXOP1 _v ->
        _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v _menhir_env._menhir_endp
    | INFIXOP2 _v ->
        _menhir_run204 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v _menhir_env._menhir_endp
    | INFIXOP3 _v ->
        _menhir_run203 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v _menhir_env._menhir_endp
    | INFIXOP4 _v ->
        _menhir_run202 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v _menhir_env._menhir_endp
    | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, x, _endpos_x_) = _menhir_stack in
        let _endpos = _endpos_x_ in
        let _v : (Input.operation list) =     ( [ x ] ) in
        _menhir_goto_nonempty_list_name_or_op_ _menhir_env _menhir_stack _menhir_s _v _endpos
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState208

and _menhir_goto_name_or_prefix : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.operation) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _endpos) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | PREFIXOP _v ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, x, _endpos_x_) = _menhir_stack in
        let _endpos = _endpos_x_ in
        let _v : (Input.operation list) =     ( [ x ] ) in
        _menhir_goto_nonempty_list_name_or_prefix_ _menhir_env _menhir_stack _menhir_s _v _endpos
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143

and _menhir_goto_nonempty_list_name_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.variable list) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    match _menhir_s with
    | MenhirState151 | MenhirState154 | MenhirState39 | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let vs = _v in
        let _endpos_vs_ = _endpos in
        let _v : (Input.variable list) =     ( vs ) in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState39 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | EXISTS ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_startp
                | FALSE ->
                    _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | FORALL ->
                    _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_startp
                | IDENT _v ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | LPAREN ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_startp
                | NOT ->
                    _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_startp
                | PREFIXOP _v ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | TRUE ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState41)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState43 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | EXISTS ->
                    _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_startp
                | FALSE ->
                    _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | FORALL ->
                    _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_startp
                | IDENT _v ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | LPAREN ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_startp
                | NOT ->
                    _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_startp
                | PREFIXOP _v ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | TRUE ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState45 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState45)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState151 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | EXISTS ->
                    _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _menhir_env._menhir_startp
                | FALSE ->
                    _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | FORALL ->
                    _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _menhir_env._menhir_startp
                | IDENT _v ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | LPAREN ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _menhir_env._menhir_startp
                | NOT ->
                    _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _menhir_env._menhir_startp
                | PREFIXOP _v ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | TRUE ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState153 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState153)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState154 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | EXISTS ->
                    _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_startp
                | FALSE ->
                    _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | FORALL ->
                    _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_startp
                | IDENT _v ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | LPAREN ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_startp
                | NOT ->
                    _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_startp
                | PREFIXOP _v ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | TRUE ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState156)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            _menhir_fail ())
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let xs = _v in
        let _endpos_xs_ = _endpos in
        let (_menhir_stack, _menhir_s, x, _startpos_x_, _endpos_x_) = _menhir_stack in
        let _endpos = _endpos_xs_ in
        let _v : (Input.variable list) =     ( x :: xs ) in
        _menhir_goto_nonempty_list_name_ _menhir_env _menhir_stack _menhir_s _v _endpos
    | MenhirState213 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let lst = _v in
        let _endpos_lst_ = _endpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_lst_ in
        let _v : (Input.theory_entry') =     ( Input.Constant lst ) in
        _menhir_goto_plain_theory_entry _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce89 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.operation) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, x, _startpos_x_, _endpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.term') =     ( Input.Var x ) in
    _menhir_goto_plain_simple_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _menhir_env._menhir_startp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState4

and _menhir_goto_plain_atomic_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState0 | MenhirState38 | MenhirState41 | MenhirState106 | MenhirState100 | MenhirState91 | MenhirState75 | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce73 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState193 | MenhirState122 | MenhirState120 | MenhirState115 | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce73 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState219 | MenhirState149 | MenhirState150 | MenhirState153 | MenhirState185 | MenhirState179 | MenhirState173 | MenhirState166 | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND | IFF | IMPLY | OR ->
            _menhir_reduce73 _menhir_env (Obj.magic _menhir_stack)
        | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, f, _startpos_f_, _endpos_f_) = _menhir_stack in
            let _startpos = _startpos_f_ in
            let _endpos = _endpos_f_ in
            let _v : (Input.formula') =     ( f ) in
            _menhir_goto_plain_negation_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce7 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Input.theory_entry list) =     ( [] ) in
    _menhir_goto_list_terminated_theory_entry_DOT__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run140 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | PREFIXOP _v ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState140

and _menhir_run146 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | COLON ->
        _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState146

and _menhir_run201 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | INFIXOP0 _v ->
        _menhir_run206 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v _menhir_env._menhir_endp
    | INFIXOP1 _v ->
        _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v _menhir_env._menhir_endp
    | INFIXOP2 _v ->
        _menhir_run204 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v _menhir_env._menhir_endp
    | INFIXOP3 _v ->
        _menhir_run203 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v _menhir_env._menhir_endp
    | INFIXOP4 _v ->
        _menhir_run202 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState201

and _menhir_run211 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | PREFIXOP _v ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState211

and _menhir_run213 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState213

and _menhir_run215 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | INFIXOP0 _v ->
        _menhir_run206 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v _menhir_env._menhir_endp
    | INFIXOP1 _v ->
        _menhir_run205 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v _menhir_env._menhir_endp
    | INFIXOP2 _v ->
        _menhir_run204 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v _menhir_env._menhir_endp
    | INFIXOP3 _v ->
        _menhir_run203 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v _menhir_env._menhir_endp
    | INFIXOP4 _v ->
        _menhir_run202 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState215

and _menhir_run217 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState217 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | COLON ->
        _menhir_reduce39 _menhir_env (Obj.magic _menhir_stack) MenhirState217
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState217

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState222 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState219 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState217 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState215 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState213 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState211 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState201 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState193 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState185 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState179 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState173 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState166 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState154 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState153 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState151 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState150 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState149 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState146 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState139 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR
    | MenhirState127 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState120 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState115 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState106 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState81 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState80 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState53 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState51 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState49 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState47 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState45 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState41 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState39 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState3 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _startpos__1_ = _startpos in
    let _endpos__1_ = _endpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Input.formula') =     ( Input.True ) in
    _menhir_goto_plain_atomic_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _menhir_env._menhir_startp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState2

and _menhir_run38 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let x = _v in
    let _startpos_x_ = _startpos in
    let _endpos_x_ = _endpos in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.operation) =               ( x ) in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState81 | MenhirState83 | MenhirState59 | MenhirState57 | MenhirState55 | MenhirState53 | MenhirState51 | MenhirState49 | MenhirState47 | MenhirState2 | MenhirState3 | MenhirState9 | MenhirState24 | MenhirState22 | MenhirState20 | MenhirState18 | MenhirState16 | MenhirState11 | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState8 in
            let _startpos = _menhir_env._menhir_startp in
            let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState9)
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | INFIXOP4 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce89 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState8)
    | MenhirState80 | MenhirState8 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce89 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState219 | MenhirState149 | MenhirState150 | MenhirState153 | MenhirState156 | MenhirState193 | MenhirState179 | MenhirState185 | MenhirState173 | MenhirState166 | MenhirState0 | MenhirState38 | MenhirState41 | MenhirState45 | MenhirState115 | MenhirState122 | MenhirState120 | MenhirState116 | MenhirState100 | MenhirState106 | MenhirState91 | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState80 in
            let _startpos = _menhir_env._menhir_startp in
            let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81)
        | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | INFIXOP4 _ | NOTEQUAL ->
            _menhir_reduce89 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80)
    | MenhirState213 | MenhirState151 | MenhirState154 | MenhirState39 | MenhirState127 | MenhirState43 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | COMMA | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, x, _startpos_x_, _endpos_x_) = _menhir_stack in
            let _endpos = _endpos_x_ in
            let _v : (Input.variable list) =     ( [ x ] ) in
            _menhir_goto_nonempty_list_name_ _menhir_env _menhir_stack _menhir_s _v _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState127)
    | MenhirState211 | MenhirState140 | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, n, _startpos_n_, _endpos_n_) = _menhir_stack in
        let _endpos = _endpos_n_ in
        let _v : (Input.operation) =     ( n ) in
        _menhir_goto_name_or_prefix _menhir_env _menhir_stack _menhir_s _v _endpos
    | MenhirState215 | MenhirState201 | MenhirState208 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, n, _startpos_n_, _endpos_n_) = _menhir_stack in
        let _endpos = _endpos_n_ in
        let _v : (Input.operation) =     ( n ) in
        _menhir_goto_name_or_op _menhir_env _menhir_stack _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_run39 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState39 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState39

and _menhir_run42 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _startpos__1_ = _startpos in
    let _endpos__1_ = _endpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Input.formula') =     ( Input.False ) in
    _menhir_goto_plain_atomic_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_run43 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState43 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState43

and _menhir_goto_option_theory_name_ : _menhir_env -> 'ttv_tail -> (Input.theory_name option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AXIOM ->
        _menhir_run217 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_startp
    | BINARY ->
        _menhir_run215 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_startp
    | CONSTANT ->
        _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_startp
    | PREDICATE ->
        _menhir_run211 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_startp
    | RELATION ->
        _menhir_run201 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_startp
    | THEOREM ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_startp
    | UNARY ->
        _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _menhir_env._menhir_startp
    | EOF ->
        _menhir_reduce7 _menhir_env (Obj.magic _menhir_stack) MenhirState139
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139

and _menhir_discard : _menhir_env -> token =
  fun _menhir_env ->
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = _menhir_env._menhir_lexer lexbuf in
    _menhir_env._menhir_token <- _tok;
    _menhir_env._menhir_startp <- lexbuf.Lexing.lex_start_p;
    _menhir_env._menhir_endp <- lexbuf.Lexing.lex_curr_p;
    let shifted = Pervasives.(+) _menhir_env._menhir_shifted 1 in
    if Pervasives.(>=) shifted 0 then
      _menhir_env._menhir_shifted <- shifted;
    _tok

and _menhir_init : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> _menhir_env =
  fun lexer lexbuf ->
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_startp = lexbuf.Lexing.lex_start_p;
      _menhir_endp = lexbuf.Lexing.lex_curr_p;
      _menhir_shifted = max_int;
      }

and formula : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Input.formula) =
  fun lexer lexbuf ->
    let _menhir_env = _menhir_init lexer lexbuf in
    Obj.magic (let _menhir_stack = () in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EXISTS ->
        _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

and theory : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Input.theory) =
  fun lexer lexbuf ->
    let _menhir_env = _menhir_init lexer lexbuf in
    Obj.magic (let _menhir_stack = () in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | THEORY ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _tok = _menhir_discard _menhir_env in
        (match _tok with
        | IDENT _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _startpos = _menhir_env._menhir_startp in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _startpos, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | DOT ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _ = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, n, _startpos_n_, _endpos_n_) = _menhir_stack in
                let _v : (Input.theory_name) =     ( n ) in
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = Obj.magic _menhir_stack in
                let x = _v in
                let _v : (Input.theory_name option) =     ( Some x ) in
                _menhir_goto_option_theory_name_ _menhir_env _menhir_stack _v
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                raise _eRR)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            raise _eRR)
    | AXIOM | BINARY | CONSTANT | EOF | PREDICATE | RELATION | THEOREM | UNARY ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _v : (Input.theory_name option) =     ( None ) in
        _menhir_goto_option_theory_name_ _menhir_env _menhir_stack _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR)




