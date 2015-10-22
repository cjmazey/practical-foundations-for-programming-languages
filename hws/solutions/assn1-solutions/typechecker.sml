structure TypeChecker : TYPECHECKER =
struct
  exception TypeError

  type context = Type.t Context.map
	
  fun equiv t1 t2 = Type.aequiv (t1, t2)

  fun checktype ctx e = 
    let 
      val num : Type.t = Type.$$(TypeOps.NUM,[])
      val str : Type.t = Type.$$(TypeOps.STR,[])
    in 
      (case Term.out e of
          Term.$((TermOps.Num n),_) => num
        | Term.$((TermOps.Str s),_) => str
        | Term.$((TermOps.Plus),[e1, e2]) => 
          if (equiv (checktype ctx e1) num 
              andalso equiv (checktype ctx e2) num) 
          then num
          else raise TypeError
        | Term.$((TermOps.Times),[e1, e2]) => 
          if (equiv (checktype ctx e1) num 
              andalso equiv (checktype ctx e2) num) 
          then num
          else raise TypeError
        | Term.$((TermOps.Cat), [e1, e2]) => 
          if (equiv (checktype ctx e1) str
              andalso  equiv (checktype ctx e2) str) 
          then str
          else raise TypeError
        | Term.$((TermOps.Len), [e1]) => 
          if (equiv (checktype ctx e1) str) 
          then num
          else raise TypeError
        | Term.$((TermOps.Let), [e1, e2]) =>
		      let
		        val t1 = checktype ctx e1
		        val abs = Term.out e2
		        val Term.\(var,e3) = abs
		        val ctx' = Context.insert(ctx, var, t1)
		      in
		        checktype ctx' e3
          end       
        | Term.`(x) =>          
           (case Context.find(ctx, x) of 
              SOME t => t
            | NONE => raise TypeError 
           )
        | Term.\(x, e1) => raise TypeError   
        | _ => raise TypeError
      )
    end
end
