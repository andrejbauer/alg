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
  | MenhirState170
  | MenhirState167
  | MenhirState165
  | MenhirState163
  | MenhirState161
  | MenhirState159
  | MenhirState156
  | MenhirState149
  | MenhirState143
  | MenhirState138
  | MenhirState136
  | MenhirState132
  | MenhirState131
  | MenhirState122
  | MenhirState116
  | MenhirState107
  | MenhirState99
  | MenhirState97
  | MenhirState96
  | MenhirState91
  | MenhirState75
  | MenhirState73
  | MenhirState71
  | MenhirState69
  | MenhirState67
  | MenhirState65
  | MenhirState63
  | MenhirState61
  | MenhirState59
  | MenhirState57
  | MenhirState55
  | MenhirState54
  | MenhirState40
  | MenhirState38
  | MenhirState36
  | MenhirState34
  | MenhirState32
  | MenhirState27
  | MenhirState25
  | MenhirState24
  | MenhirState21
  | MenhirState20
  | MenhirState19
  | MenhirState17
  | MenhirState14
  | MenhirState11
  | MenhirState7
  | MenhirState6

  
let _eRR =
  Error

let rec _menhir_goto_plain_quantified_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState57 | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _startpos_f_ = _startpos in
        let _endpos_f_ = _endpos in
        let _startpos = _startpos_f_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( f ) in
        _menhir_goto_plain_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState54 | MenhirState107 | MenhirState91 ->
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
        let _v : (Input.formula) =                                                             ( _1 ) in
        (match _menhir_s with
        | MenhirState91 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let f2 = _v in
            let _endpos_f2_ = _endpos in
            let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
            let _startpos = _startpos_f1_ in
            let _endpos = _endpos_f2_ in
            let _v : (Input.formula') =     ( Input.Or (f1, f2) ) in
            _menhir_goto_plain_or_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | MenhirState107 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let f2 = _v in
            let _endpos_f2_ = _endpos in
            let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
            let _startpos = _startpos_f1_ in
            let _endpos = _endpos_f2_ in
            let _v : (Input.formula') =     ( Input.And (f1, f2) ) in
            _menhir_goto_plain_and_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | MenhirState54 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let f = _v in
            let _endpos_f_ = _endpos in
            let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_f_ in
            let _v : (Input.formula') =     ( Input.Not f ) in
            _menhir_goto_plain_negation_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            _menhir_fail ())
    | MenhirState167 | MenhirState17 | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _startpos_f_ = _startpos in
        let _endpos_f_ = _endpos in
        let _startpos = _startpos_f_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( f ) in
        _menhir_goto_plain_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_run138 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | FALSE ->
        _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState138

and _menhir_reduce76 : _menhir_env -> ('ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position) * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_), _, f2, _startpos_f2_, _endpos_f2_) = _menhir_stack in
    let _startpos = _startpos_f1_ in
    let _endpos = _endpos_f2_ in
    let _v : (Input.formula') =     ( Input.Or (f1, f2) ) in
    _menhir_goto_plain_or_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_run107 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107

and _menhir_goto_plain_formula_noquant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
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
    let _endpos__1_ = _endpos in
    let _endpos = _endpos__1_ in
    let _v : (Input.formula) =                                                       ( _1 ) in
    match _menhir_s with
    | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _endpos_f_ = _endpos in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _, xs) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( Input.Exists (xs, f) ) in
        _menhir_goto_plain_quantified_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _endpos_f_ = _endpos in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _, xs) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( Input.Forall (xs, f) ) in
        _menhir_goto_plain_quantified_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_run91 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91

and _menhir_run116 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116

and _menhir_run132 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | FALSE ->
        _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState132

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

and _menhir_reduce50 : _menhir_env -> (((('ttv_tail * _menhir_state * (Input.operation) * Lexing.position * Lexing.position) * _menhir_state * Lexing.position) * _menhir_state * (Input.term) * Lexing.position * Lexing.position) * _menhir_state * (Input.term) * Lexing.position * Lexing.position) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((((_menhir_stack, _menhir_s, op, _startpos_op_, _endpos_op_), _, _startpos__2_), _, t1, _startpos_t1_, _endpos_t1_), _, t2, _startpos_t2_, _endpos_t2_), _endpos__6_) = _menhir_stack in
    let _startpos = _startpos_op_ in
    let _endpos = _endpos__6_ in
    let _v : (Input.term') =     ( Input.BinaryOp (op, t1, t2) ) in
    _menhir_goto_plain_app_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce90 : _menhir_env -> (('ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position) * (string) * Lexing.position) * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> 'ttv_return =
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

and _menhir_run27 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _v _endpos ->
    let _menhir_stack = (_menhir_stack, _v, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27

and _menhir_run32 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _v _endpos ->
    let _menhir_stack = (_menhir_stack, _v, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState32

and _menhir_run34 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _v _endpos ->
    let _menhir_stack = (_menhir_stack, _v, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34

and _menhir_run36 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _v _endpos ->
    let _menhir_stack = (_menhir_stack, _v, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36

and _menhir_run38 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term) * Lexing.position * Lexing.position -> (string) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _v _endpos ->
    let _menhir_stack = (_menhir_stack, _v, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38

and _menhir_goto_plain_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
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
    let _endpos__1_ = _endpos in
    let _endpos = _endpos__1_ in
    let _v : (Input.formula) =                                       ( _1 ) in
    match _menhir_s with
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f2 = _v in
        let _endpos_f2_ = _endpos in
        let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
        let _startpos = _startpos_f1_ in
        let _endpos = _endpos_f2_ in
        let _v : (Input.formula') =     ( Input.Imply (f1, f2) ) in
        _menhir_goto_plain_imply_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let a = _v in
        let _endpos_a_ = _endpos in
        let ((_menhir_stack, _menhir_s, _startpos__1_), _, n) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_a_ in
        let _v : (Input.theory_entry') =     ( Input.Axiom (n, a) ) in
        _menhir_goto_plain_theory_entry _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState167 ->
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

and _menhir_goto_plain_imply_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState57 | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _startpos_f_ = _startpos in
        let _endpos_f_ = _endpos in
        let _startpos = _startpos_f_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( f ) in
        _menhir_goto_plain_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState167 | MenhirState17 | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _startpos_f_ = _startpos in
        let _endpos_f_ = _endpos in
        let _startpos = _startpos_f_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( f ) in
        _menhir_goto_plain_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce9 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula') * Lexing.position * Lexing.position -> 'ttv_return =
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
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | IFF | IMPLY | OR ->
            _menhir_reduce76 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState167 | MenhirState17 | MenhirState57 | MenhirState61 | MenhirState116 | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run107 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState136 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
        | DOT | OR ->
            _menhir_reduce76 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack)
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
    | MenhirState57 | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IFF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | FALSE ->
                _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131)
        | IMPLY ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState167 | MenhirState17 | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IFF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | FALSE ->
                _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState122 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122)
        | IMPLY ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OR ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | FALSE ->
                _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState136)
        | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_), _, f2, _startpos_f2_, _endpos_f2_) = _menhir_stack in
            let _startpos = _startpos_f1_ in
            let _endpos = _endpos_f2_ in
            let _v : (Input.formula') =     ( Input.Iff (f1, f2) ) in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let f = _v in
            let _startpos_f_ = _startpos in
            let _endpos_f_ = _endpos in
            let _startpos = _startpos_f_ in
            let _endpos = _endpos_f_ in
            let _v : (Input.formula') =     ( f ) in
            _menhir_goto_plain_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
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
    let _startpos__1_ = _startpos in
    let _endpos__1_ = _endpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Input.term) =                                 ( _1 ) in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40)
        | INFIXOP0 _v ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce94 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce93 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce92 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce91 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce90 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP0 _v ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _endpos) in
            let _ = _menhir_discard _menhir_env in
            _menhir_reduce50 _menhir_env (Obj.magic _menhir_stack)
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
        | INFIXOP0 _v ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState167 | MenhirState17 | MenhirState54 | MenhirState57 | MenhirState138 | MenhirState136 | MenhirState131 | MenhirState132 | MenhirState122 | MenhirState116 | MenhirState107 | MenhirState91 | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75)
        | INFIXOP0 _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73)
        | INFIXOP1 _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71)
        | INFIXOP2 _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState69 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState69)
        | INFIXOP3 _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67)
        | INFIXOP4 _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _endpos = _menhir_env._menhir_endp in
            let _menhir_stack = (_menhir_stack, _v, _endpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65)
        | NOTEQUAL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP0 _v ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
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
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
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
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | NOTEQUAL ->
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
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | NOTEQUAL ->
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
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
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
    | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | EQUAL | INFIXOP0 _ | NOTEQUAL ->
            _menhir_reduce90 _menhir_env (Obj.magic _menhir_stack)
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
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP0 _v ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
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
    | MenhirState97 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState99 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState99)
        | INFIXOP0 _v ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | INFIXOP0 _v ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP1 _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP2 _v ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP3 _v ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
        | INFIXOP4 _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) _v _menhir_env._menhir_endp
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
                _menhir_reduce50 _menhir_env (Obj.magic _menhir_stack)
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

and _menhir_goto_plain_or_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState167 | MenhirState17 | MenhirState57 | MenhirState116 | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _startpos_f_ = _startpos in
        let _endpos_f_ = _endpos in
        let _startpos = _startpos_f_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( f ) in
        _menhir_goto_plain_imply_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState122 ->
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
        let _v : (Input.formula) =                                             ( _1 ) in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f2 = _v in
        let _endpos_f2_ = _endpos in
        let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
        let _startpos = _startpos_f1_ in
        let _endpos = _endpos_f2_ in
        let _v : (Input.formula') =     ( Input.Iff (f1, f2) ) in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _startpos_f_ = _startpos in
        let _endpos_f_ = _endpos in
        let _startpos = _startpos_f_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( f ) in
        _menhir_goto_plain_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_and_formula_noquant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState167 | MenhirState17 | MenhirState57 | MenhirState131 | MenhirState122 | MenhirState116 | MenhirState61 ->
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
            _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState136 | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce9 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_term : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.term') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState167 | MenhirState17 | MenhirState54 | MenhirState57 | MenhirState138 | MenhirState136 | MenhirState131 | MenhirState132 | MenhirState122 | MenhirState116 | MenhirState107 | MenhirState99 | MenhirState91 | MenhirState61 | MenhirState75 | MenhirState73 | MenhirState71 | MenhirState69 | MenhirState67 | MenhirState65 | MenhirState63 | MenhirState40 | MenhirState38 | MenhirState36 | MenhirState34 | MenhirState32 | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce19 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState97 | MenhirState20 | MenhirState25 ->
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
            _menhir_reduce19 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_and_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState167 | MenhirState17 | MenhirState57 | MenhirState122 | MenhirState116 | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _startpos_f_ = _startpos in
        let _endpos_f_ = _endpos in
        let _startpos = _startpos_f_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( f ) in
        _menhir_goto_plain_or_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState91 ->
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
        let _v : (Input.formula) =                                               ( _1 ) in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f2 = _v in
        let _endpos_f2_ = _endpos in
        let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
        let _startpos = _startpos_f1_ in
        let _endpos = _endpos_f2_ in
        let _v : (Input.formula') =     ( Input.Or (f1, f2) ) in
        _menhir_goto_plain_or_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | _ ->
        _menhir_fail ()

and _menhir_goto_plain_negation_formula_noquant : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState167 | MenhirState17 | MenhirState57 | MenhirState136 | MenhirState131 | MenhirState122 | MenhirState116 | MenhirState91 | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _startpos_f_ = _startpos in
        let _endpos_f_ = _endpos in
        let _startpos = _startpos_f_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( f ) in
        _menhir_goto_plain_and_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState54 | MenhirState138 | MenhirState132 | MenhirState107 ->
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
        | MenhirState138 | MenhirState107 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let f2 = _v in
            let _endpos_f2_ = _endpos in
            let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
            let _startpos = _startpos_f1_ in
            let _endpos = _endpos_f2_ in
            let _v : (Input.formula') =     ( Input.And (f1, f2) ) in
            _menhir_goto_plain_and_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | MenhirState54 | MenhirState132 ->
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

and _menhir_reduce49 : _menhir_env -> ('ttv_tail * _menhir_state * (Input.operation) * Lexing.position * Lexing.position) * _menhir_state * (Input.term) * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((_menhir_stack, _menhir_s, op, _startpos_op_, _endpos_op_), _, t, _endpos_t_) = _menhir_stack in
    let _startpos = _startpos_op_ in
    let _endpos = _endpos_t_ in
    let _v : (Input.term') =     ( Input.UnaryOp (op, t) ) in
    _menhir_goto_plain_app_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_goto_plain_app_term : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.term') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState19 | MenhirState21 ->
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
    | MenhirState167 | MenhirState17 | MenhirState54 | MenhirState57 | MenhirState138 | MenhirState136 | MenhirState131 | MenhirState132 | MenhirState122 | MenhirState116 | MenhirState107 | MenhirState97 | MenhirState99 | MenhirState91 | MenhirState61 | MenhirState75 | MenhirState73 | MenhirState71 | MenhirState69 | MenhirState67 | MenhirState65 | MenhirState63 | MenhirState20 | MenhirState25 | MenhirState40 | MenhirState38 | MenhirState36 | MenhirState34 | MenhirState32 | MenhirState27 ->
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

and _menhir_goto_plain_negation_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    match _menhir_s with
    | MenhirState167 | MenhirState17 | MenhirState57 | MenhirState122 | MenhirState116 | MenhirState91 | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let f = _v in
        let _startpos_f_ = _startpos in
        let _endpos_f_ = _endpos in
        let _startpos = _startpos_f_ in
        let _endpos = _endpos_f_ in
        let _v : (Input.formula') =     ( f ) in
        _menhir_goto_plain_and_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState54 | MenhirState107 ->
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
        let _v : (Input.formula) =                                                         ( _1 ) in
        (match _menhir_s with
        | MenhirState107 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let f2 = _v in
            let _endpos_f2_ = _endpos in
            let (_menhir_stack, _menhir_s, f1, _startpos_f1_, _endpos_f1_) = _menhir_stack in
            let _startpos = _startpos_f1_ in
            let _endpos = _endpos_f2_ in
            let _v : (Input.formula') =     ( Input.And (f1, f2) ) in
            _menhir_goto_plain_and_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | MenhirState54 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let f = _v in
            let _endpos_f_ = _endpos in
            let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
            let _startpos = _startpos__1_ in
            let _endpos = _endpos_f_ in
            let _v : (Input.formula') =     ( Input.Not f ) in
            _menhir_goto_plain_negation_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
        | _ ->
            _menhir_fail ())
    | _ ->
        _menhir_fail ()

and _menhir_reduce72 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.formula') * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, f, _startpos_f_, _endpos_f_) = _menhir_stack in
    let _startpos = _startpos_f_ in
    let _endpos = _endpos_f_ in
    let _v : (Input.formula') =     ( f ) in
    _menhir_goto_plain_negation_formula_noquant _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_reduce18 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term') * Lexing.position * Lexing.position -> 'ttv_return =
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
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce49 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, op, _startpos_op_, _endpos_op_), _, t, _endpos_t_) = _menhir_stack in
        let _startpos = _startpos_op_ in
        let _endpos = _endpos_t_ in
        let _v : (Input.formula') =     ( Input.UnaryPr (op, t) ) in
        _menhir_goto_plain_predicate _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState96 ->
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
            _menhir_reduce49 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce51 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.term') * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, t, _startpos_t_, _endpos_t_) = _menhir_stack in
    let _startpos = _startpos_t_ in
    let _endpos = _endpos_t_ in
    let _v : (Input.term') =     ( t ) in
    _menhir_goto_plain_app_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_goto_plain_atomic_formula : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.formula') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState167 | MenhirState17 | MenhirState54 | MenhirState57 | MenhirState122 | MenhirState116 | MenhirState107 | MenhirState91 | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | AND | IFF | IMPLY | OR ->
            _menhir_reduce72 _menhir_env (Obj.magic _menhir_stack)
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
    | MenhirState138 | MenhirState136 | MenhirState131 | MenhirState132 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce72 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_name_or_op_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.operation list) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    match _menhir_s with
    | MenhirState149 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let lst = _v in
        let _endpos_lst_ = _endpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_lst_ in
        let _v : (Input.theory_entry') =     ( Input.Relation lst ) in
        _menhir_goto_plain_theory_entry _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let xs = _v in
        let _endpos_xs_ = _endpos in
        let (_menhir_stack, _menhir_s, x, _endpos_x_) = _menhir_stack in
        let _endpos = _endpos_xs_ in
        let _v : (Input.operation list) =     ( x :: xs ) in
        _menhir_goto_nonempty_list_name_or_op_ _menhir_env _menhir_stack _menhir_s _v _endpos
    | MenhirState163 ->
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
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_startp
        | BINARY ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_startp
        | CONSTANT ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_startp
        | PREDICATE ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_startp
        | RELATION ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_startp
        | THEOREM ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_startp
        | UNARY ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _menhir_env._menhir_startp
        | EOF ->
            _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState170
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState170)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_plain_simple_term : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.term') -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    match _menhir_s with
    | MenhirState167 | MenhirState17 | MenhirState54 | MenhirState57 | MenhirState138 | MenhirState136 | MenhirState131 | MenhirState132 | MenhirState122 | MenhirState116 | MenhirState107 | MenhirState97 | MenhirState99 | MenhirState91 | MenhirState61 | MenhirState75 | MenhirState73 | MenhirState71 | MenhirState69 | MenhirState67 | MenhirState65 | MenhirState63 | MenhirState20 | MenhirState25 | MenhirState40 | MenhirState38 | MenhirState36 | MenhirState34 | MenhirState32 | MenhirState27 | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce51 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState96 | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce18 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | INFIXOP4 _ | NOTEQUAL ->
            _menhir_reduce51 _menhir_env (Obj.magic _menhir_stack)
        | AND | DOT | IFF | IMPLY | OR ->
            _menhir_reduce18 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_nonempty_list_name_or_prefix_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.operation list) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    match _menhir_s with
    | MenhirState7 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let lst = _v in
        let _endpos_lst_ = _endpos in
        let (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
        let _startpos = _startpos__1_ in
        let _endpos = _endpos_lst_ in
        let _v : (Input.theory_entry') =     ( Input.Unary lst ) in
        _menhir_goto_plain_theory_entry _menhir_env _menhir_stack _menhir_s _v _startpos _endpos
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let xs = _v in
        let _endpos_xs_ = _endpos in
        let (_menhir_stack, _menhir_s, x, _endpos_x_) = _menhir_stack in
        let _endpos = _endpos_xs_ in
        let _v : (Input.operation list) =     ( x :: xs ) in
        _menhir_goto_nonempty_list_name_or_prefix_ _menhir_env _menhir_stack _menhir_s _v _endpos
    | MenhirState159 ->
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

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _startpos__1_ = _startpos in
    let _endpos__1_ = _endpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Input.formula') =     ( Input.True ) in
    _menhir_goto_plain_atomic_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_run19 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _menhir_env._menhir_startp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState19

and _menhir_run54 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | EXISTS ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_startp
    | FALSE ->
        _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | FORALL ->
        _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_startp
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_startp
    | NOT ->
        _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | TRUE ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54

and _menhir_run55 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55

and _menhir_run58 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _startpos__1_ = _startpos in
    let _endpos__1_ = _endpos in
    let _startpos = _startpos__1_ in
    let _endpos = _endpos__1_ in
    let _v : (Input.formula') =     ( Input.False ) in
    _menhir_goto_plain_atomic_formula _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_run59 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59

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
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | INFIXOP0 _v ->
        _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v _menhir_env._menhir_endp
    | INFIXOP1 _v ->
        _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v _menhir_env._menhir_endp
    | INFIXOP2 _v ->
        _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v _menhir_env._menhir_endp
    | INFIXOP3 _v ->
        _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v _menhir_env._menhir_endp
    | INFIXOP4 _v ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState156 _v _menhir_env._menhir_endp
    | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, x, _endpos_x_) = _menhir_stack in
        let _endpos = _endpos_x_ in
        let _v : (Input.operation list) =     ( [ x ] ) in
        _menhir_goto_nonempty_list_name_or_op_ _menhir_env _menhir_stack _menhir_s _v _endpos
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState156

and _menhir_goto_nonempty_list_name_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.variable list) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    match _menhir_s with
    | MenhirState55 | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let vs = _v in
        let _endpos_vs_ = _endpos in
        let _v : (Input.variable list) =     ( vs ) in
        let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        (match _menhir_s with
        | MenhirState55 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | EXISTS ->
                    _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _menhir_env._menhir_startp
                | FALSE ->
                    _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | FORALL ->
                    _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _menhir_env._menhir_startp
                | IDENT _v ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | LPAREN ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _menhir_env._menhir_startp
                | NOT ->
                    _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _menhir_env._menhir_startp
                | PREFIXOP _v ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | TRUE ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState57 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState57)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | MenhirState59 ->
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | COMMA ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _tok = _menhir_discard _menhir_env in
                (match _tok with
                | EXISTS ->
                    _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_startp
                | FALSE ->
                    _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | FORALL ->
                    _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_startp
                | IDENT _v ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | LPAREN ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_startp
                | NOT ->
                    _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_startp
                | PREFIXOP _v ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
                | TRUE ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _menhir_env._menhir_startp _menhir_env._menhir_endp
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState61)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            _menhir_fail ())
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let xs = _v in
        let _endpos_xs_ = _endpos in
        let (_menhir_stack, _menhir_s, x, _startpos_x_, _endpos_x_) = _menhir_stack in
        let _endpos = _endpos_xs_ in
        let _v : (Input.variable list) =     ( x :: xs ) in
        _menhir_goto_nonempty_list_name_ _menhir_env _menhir_stack _menhir_s _v _endpos
    | MenhirState161 ->
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

and _menhir_reduce88 : _menhir_env -> 'ttv_tail * _menhir_state * (Input.operation) * Lexing.position * Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, x, _startpos_x_, _endpos_x_) = _menhir_stack in
    let _startpos = _startpos_x_ in
    let _endpos = _endpos_x_ in
    let _v : (Input.term') =     ( Input.Var x ) in
    _menhir_goto_plain_simple_term _menhir_env _menhir_stack _menhir_s _v _startpos _endpos

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _menhir_env._menhir_startp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21

and _menhir_run20 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _menhir_env._menhir_startp
    | PREFIXOP _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20

and _menhir_goto_name_or_prefix : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.operation) -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _endpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v, _endpos) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | PREFIXOP _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState11 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | DOT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, x, _endpos_x_) = _menhir_stack in
        let _endpos = _endpos_x_ in
        let _v : (Input.operation list) =     ( [ x ] ) in
        _menhir_goto_nonempty_list_name_or_prefix_ _menhir_env _menhir_stack _menhir_s _v _endpos
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState11

and _menhir_goto_option_IDENT_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (string option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | EXISTS ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_startp
            | FALSE ->
                _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | FORALL ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_startp
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState165 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COLON ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | EXISTS ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _menhir_env._menhir_startp
            | FALSE ->
                _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | FORALL ->
                _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _menhir_env._menhir_startp
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _menhir_env._menhir_startp
            | NOT ->
                _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | TRUE ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState167)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_terminated_theory_entry_DOT__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Input.theory_entry list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState170 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, x0), _, xs) = _menhir_stack in
        let _v : (Input.theory_entry list) = let x =
          let x = x0 in
              ( x )
        in
            ( x :: xs ) in
        _menhir_goto_list_terminated_theory_entry_DOT__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState6 ->
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

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let op = _v in
    let _startpos_op_ = _startpos in
    let _endpos_op_ = _endpos in
    let _endpos = _endpos_op_ in
    let _v : (Input.operation) =     ( op ) in
    _menhir_goto_name_or_prefix _menhir_env _menhir_stack _menhir_s _v _endpos

and _menhir_run150 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> 'ttv_return =
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

and _menhir_run151 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> 'ttv_return =
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

and _menhir_run152 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> 'ttv_return =
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

and _menhir_run153 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> 'ttv_return =
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

and _menhir_run154 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> 'ttv_return =
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

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> Lexing.position -> 'ttv_return =
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
    | MenhirState159 | MenhirState7 | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, n, _startpos_n_, _endpos_n_) = _menhir_stack in
        let _endpos = _endpos_n_ in
        let _v : (Input.operation) =     ( n ) in
        _menhir_goto_name_or_prefix _menhir_env _menhir_stack _menhir_s _v _endpos
    | MenhirState97 | MenhirState99 | MenhirState75 | MenhirState73 | MenhirState71 | MenhirState69 | MenhirState67 | MenhirState65 | MenhirState63 | MenhirState19 | MenhirState20 | MenhirState25 | MenhirState40 | MenhirState38 | MenhirState36 | MenhirState34 | MenhirState32 | MenhirState27 | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState24 in
            let _startpos = _menhir_env._menhir_startp in
            let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25)
        | AND | COMMA | DOT | EQUAL | IFF | IMPLY | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | INFIXOP4 _ | NOTEQUAL | OR | RPAREN ->
            _menhir_reduce88 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24)
    | MenhirState96 | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        _menhir_reduce88 _menhir_env (Obj.magic _menhir_stack)
    | MenhirState167 | MenhirState17 | MenhirState54 | MenhirState57 | MenhirState61 | MenhirState131 | MenhirState138 | MenhirState136 | MenhirState132 | MenhirState116 | MenhirState122 | MenhirState107 | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | LPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_s = MenhirState96 in
            let _startpos = _menhir_env._menhir_startp in
            let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
            let _tok = _menhir_discard _menhir_env in
            (match _tok with
            | IDENT _v ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | LPAREN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _menhir_env._menhir_startp
            | PREFIXOP _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState97)
        | EQUAL | INFIXOP0 _ | INFIXOP1 _ | INFIXOP2 _ | INFIXOP3 _ | INFIXOP4 _ | NOTEQUAL ->
            _menhir_reduce88 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState96)
    | MenhirState161 | MenhirState55 | MenhirState143 | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
        | COMMA | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, x, _startpos_x_, _endpos_x_) = _menhir_stack in
            let _endpos = _endpos_x_ in
            let _v : (Input.variable list) =     ( [ x ] ) in
            _menhir_goto_nonempty_list_name_ _menhir_env _menhir_stack _menhir_s _v _endpos
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143)
    | MenhirState163 | MenhirState149 | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, n, _startpos_n_, _endpos_n_) = _menhir_stack in
        let _endpos = _endpos_n_ in
        let _v : (Input.operation) =     ( n ) in
        _menhir_goto_name_or_op _menhir_env _menhir_stack _menhir_s _v _endpos
    | _ ->
        _menhir_fail ()

and _menhir_reduce38 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (string option) =     ( None ) in
    _menhir_goto_option_IDENT_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run15 : _menhir_env -> 'ttv_tail -> _menhir_state -> (string) -> Lexing.position -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v _startpos _endpos ->
    let _ = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let x = _v in
    let _startpos_x_ = _startpos in
    let _endpos_x_ = _endpos in
    let _v : (string option) =     ( Some x ) in
    _menhir_goto_option_IDENT_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState170 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState167 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState165 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState163 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState161 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState159 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState156 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState149 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState138 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState136 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState132 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState131 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState122 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState99 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState97 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState96 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState75 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState73 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState69 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState63 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState61 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState57 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _, _, _), _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState25 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState24 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState14 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState11 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState7 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_reduce6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Input.theory_entry list) =     ( [] ) in
    _menhir_goto_list_terminated_theory_entry_DOT__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | PREFIXOP _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7

and _menhir_run14 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState14 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | COLON ->
        _menhir_reduce38 _menhir_env (Obj.magic _menhir_stack) MenhirState14
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState14

and _menhir_run149 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | INFIXOP0 _v ->
        _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v _menhir_env._menhir_endp
    | INFIXOP1 _v ->
        _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v _menhir_env._menhir_endp
    | INFIXOP2 _v ->
        _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v _menhir_env._menhir_endp
    | INFIXOP3 _v ->
        _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v _menhir_env._menhir_endp
    | INFIXOP4 _v ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState149

and _menhir_run159 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | PREFIXOP _v ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState159

and _menhir_run161 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState161

and _menhir_run163 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | INFIXOP0 _v ->
        _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v _menhir_env._menhir_endp
    | INFIXOP1 _v ->
        _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v _menhir_env._menhir_endp
    | INFIXOP2 _v ->
        _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v _menhir_env._menhir_endp
    | INFIXOP3 _v ->
        _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v _menhir_env._menhir_endp
    | INFIXOP4 _v ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v _menhir_env._menhir_endp
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState163

and _menhir_run165 : _menhir_env -> 'ttv_tail -> _menhir_state -> Lexing.position -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _startpos ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _startpos) in
    let _tok = _menhir_discard _menhir_env in
    match _tok with
    | IDENT _v ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v _menhir_env._menhir_startp _menhir_env._menhir_endp
    | COLON ->
        _menhir_reduce38 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState165

and _menhir_goto_option_theory_name_ : _menhir_env -> 'ttv_tail -> (Input.theory_name option) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AXIOM ->
        _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_startp
    | BINARY ->
        _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_startp
    | CONSTANT ->
        _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_startp
    | PREDICATE ->
        _menhir_run159 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_startp
    | RELATION ->
        _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_startp
    | THEOREM ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_startp
    | UNARY ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _menhir_env._menhir_startp
    | EOF ->
        _menhir_reduce6 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6

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

and theory : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Input.theory) =
  fun lexer lexbuf ->
    let _menhir_env = let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_startp = lexbuf.Lexing.lex_start_p;
      _menhir_endp = lexbuf.Lexing.lex_curr_p;
      _menhir_shifted = max_int;
      } in
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




