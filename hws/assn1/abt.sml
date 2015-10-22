functor Abt(O : OPERATOR) :> ABT where type Variable.t = Var.t 
                                 where type Operator.t = O.t
=
struct
   open List_Util

   structure Variable = Var
   structure Operator = O 

   datatype 'a view = 
     ` of Variable.t
   | \ of Variable.t * 'a
   | $ of Operator.t * 'a list

   datatype t =
     FV of Var.t
   | BV of int
   | ABS of t
   | OPER of Operator.t * t list

   exception Malformed
   exception NotImplemented

   (* ... your solution goes here ... *)
   fun into x    = raise NotImplemented
   fun out x     = raise NotImplemented
   fun aequiv x  = raise NotImplemented
   fun map x y   = raise NotImplemented

end
