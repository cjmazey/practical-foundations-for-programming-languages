structure TermOps =
struct

  datatype t = Num of int | Str of string | Plus | Times | Cat | Len | Let 
               
  fun arity (Num _) = []
    | arity (Str _) = []
    | arity Plus = [0,0]
    | arity Times = [0, 0]
    | arity Cat = [0,0]
    | arity Len = [0]
    | arity Let = [0,1]
      
  fun equal (Num n1, Num n2) = (n1 = n2)
    | equal (Str s1, Str s2) = (s1 = s2)
    | equal (Plus, Plus) = true
    | equal (Times, Times) = true
    | equal (Cat, Cat) = true
    | equal (Len, Len) = true
    | equal (Let, Let) = true
    | equal _ = false

  fun toString (Num n) = Int.toString n
    | toString (Str s) = "\""^s^"\""
    | toString Plus = "plus"
    | toString Times = "times"
    | toString Cat = "cat"
    | toString Len = "len"
    | toString Let = "let"
end
