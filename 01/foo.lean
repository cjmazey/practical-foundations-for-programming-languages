inductive exp : Type :=
| var : ℕ → exp
| num : ℕ → exp
| plus : exp → exp → exp
| times : exp → exp → exp

namespace exp
  open nat

  definition X := var 0
  definition exp_ex1 : exp := plus (num 2) (times (num 3) X)
  definition exp_ex2 : exp := plus (num 2) (times (num 3) (num 4))
end exp
