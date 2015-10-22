structure CheckedDynamics : DYNAMICS =
struct

  exception RuntimeError
  exception Malformed
  exception NotImplemented

  datatype D = Step of Term.t | Val | Err

  (* ... your solution goes here ... *)
  datatype d = ToBeImplemented
  
  fun view e        = raise NotImplemented
  fun trystep e     = raise NotImplemented
  fun eval e        = raise NotImplemented
end
