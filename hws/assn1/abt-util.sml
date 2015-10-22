functor ABT_Util(A : ABT) : ABT_UTIL = 
struct
  open A 

  (* ... your solution goes here ... *)
   exception NotImplemented

   fun freevars e     = raise NotImplemented  
   fun subst a x b    = raise NotImplemented  
   fun `` e           = raise NotImplemented  
   fun \\ e           = raise NotImplemented  
   fun $$ e           = raise NotImplemented  
   fun toString e     = raise NotImplemented 
end
