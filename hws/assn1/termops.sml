structure TermOps =
struct

  datatype t = Num of int | Str of string | Plus | Times | Cat | Len | Let 
               
  (* ... your solution goes here ... *)
   exception NotImplemented
   fun arity e = raise NotImplemented
   fun equal e = raise NotImplemented

  fun toString (Num n) = Int.toString n
    | toString (Str s) = "\""^s^"\""
    | toString Plus = "plus"
    | toString Times = "times"
    | toString Cat = "cat"
    | toString Len = "len"
    | toString Let = "let"
end
