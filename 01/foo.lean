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

  theorem structural_induction :
      ∀ P : exp → Prop,
      (∀ n : ℕ, P (var n)) →
      (∀ n : ℕ, P (num n)) →
      (∀ a₁ a₂ : exp, P a₁ → P a₂ → P (plus a₁ a₂)) →
      (∀ a₁ a₂ : exp, P a₁ → P a₂ → P (times a₁ a₂)) →
      ∀ a : exp, P a :=
    @exp.rec
end exp
