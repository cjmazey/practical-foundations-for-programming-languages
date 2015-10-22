structure CheckedDynamics : DYNAMICS =
struct

  exception RuntimeError
  exception Malformed

  datatype d = STEP of Term.t | VAL | ERR
  datatype D = Step of Term.t | Val | Err

  fun view d1 = (case d1 of 
    STEP t1 => Step t1
    | VAL => Val
    | ERR => Err
  )

  fun is_num e = 
    (case Term.out e of 
      Term.$((TermOps.Num n), []) => true
    | _ => false)

  fun is_str e = 
    (case Term.out e of 
      Term.$((TermOps.Str s), []) => true
    | _ => false)

  (*Plus(e1, e2) step when e1 val and e2 val*)
  fun addnumval e1 e2 = 
    (case (Term.out e1, Term.out e2) of
          (Term.$((TermOps.Num n1),_), Term.$(TermOps.Num n2, _)) => STEP(Term.$$(TermOps.Num (n1+n2),[]))
        | _ => ERR
    )
 
  (*Times(e1, e2) step when e1 val and e2 val*)
  fun timesnumval e1 e2 = 
    (case (Term.out e1, Term.out e2) of
          (Term.$((TermOps.Num n1),_), Term.$(TermOps.Num n2, _)) => STEP(Term.$$(TermOps.Num (n1*n2),[]))
        | _ => ERR
    )
 
  (*Cat(e1, e2) step when e1 val and e2 val*)
  fun catstrval e1 e2 = 
    (case (Term.out e1, Term.out e2) of
          (Term.$((TermOps.Str s1),_), Term.$(TermOps.Str s2, _)) => STEP(Term.$$(TermOps.Str (s1^s2),[]))
        | _ => ERR
    )

  (*Len(s) step when e1 val and e2 val*)
  fun lenstrval e  = 
    (case Term.out e of
          Term.$((TermOps.Str s),_) => STEP(Term.$$(TermOps.Num (String.size(s)),[]))
        | _ => ERR
    )

  (*Step for expression e which returns either STEP(e'), VAL or ERR*)
  fun trystep e = 
        (case Term.out e of
          Term.$((TermOps.Num n),_) => VAL
        | Term.$((TermOps.Str n),_) => VAL
        | Term.$((TermOps.Plus),[e1, e2]) => 
            (case trystep e1 of 
                  STEP(e1') => STEP(Term.$$((TermOps.Plus),[e1', e2]))
                | VAL => (if is_num e1 then 
                    (case trystep e2 of
                      STEP(e2') => STEP(Term.$$((TermOps.Plus),[e1, e2']))
                    | VAL => addnumval e1 e2
                    | ERR => ERR) else ERR)
                | ERR => ERR
            )
        | Term.$((TermOps.Times),[e1, e2]) => 
            (case trystep e1 of 
                  STEP(e1') => STEP(Term.$$((TermOps.Times),[e1', e2]))
                | VAL => (if is_num e1 then 
                  (case trystep e2 of
                    STEP(e2') => STEP(Term.$$((TermOps.Times),[e1, e2']))
                  | VAL => timesnumval e1 e2
                  | ERR => ERR) else ERR)
                | ERR => ERR
            )
        | Term.$((TermOps.Cat),[e1, e2]) => 
            (case trystep e1 of 
                  STEP(e1') => STEP(Term.$$((TermOps.Cat),[e1', e2]))
                | VAL => (if is_str e1 then 
                  (case trystep e2 of
                    STEP(e2') => STEP(Term.$$((TermOps.Cat),[e1, e2']))
                  | VAL => catstrval e1 e2
                  | ERR => ERR) else ERR)
                | ERR => ERR
            )
        | Term.$((TermOps.Len),[e1]) => 
            (case trystep e1 of 
                  STEP(e1') => STEP(Term.$$((TermOps.Len),[e1']))
                | VAL => lenstrval e1
                | ERR => ERR
            )
        | Term.$((TermOps.Let),[e1,e2]) =>
           (case trystep e1 of
                 STEP(e1') => STEP(Term.$$((TermOps.Let,[e1', e2])))
                | VAL =>
                    let
                        val abs = Term.out e2
                        val Term.\ (var,e3) = abs
                    in
                        STEP(Term.subst e1 var e3)
                    end
               | ERR => ERR
           )
        | _ => raise Malformed
        )

  fun eval e = 
    case trystep e of
          STEP e' => eval e'
        | VAL => e
        | ERR => raise RuntimeError


end
