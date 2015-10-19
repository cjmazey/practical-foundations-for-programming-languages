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

namespace shuffling

  inductive card : Type :=
  | h : card
  | s : card
  | c : card
  | d : card

  open card

  inductive stack : Type :=
  | nil : stack
  | cons : card → stack → stack

  open stack

  inductive unshuffle : stack → stack → stack → Prop :=
  | unz : unshuffle nil nil nil
  | unr : ∀ {s₁ s₂ s₃ : stack} (c : card), unshuffle s₁ s₂ s₃ →
              unshuffle (cons c s₁) s₂ (cons c s₃)
  | unl : ∀ {s₁ s₂ s₃ : stack} (c : card), unshuffle s₁ s₂ s₃ →
              unshuffle (cons c s₁) (cons c s₂) s₃

  open unshuffle

  -- Task 2.1
  example : unshuffle (cons h (cons s (cons s (cons d nil))))
                      (cons s (cons d nil))
                      (cons h (cons s nil)) :=
  unr h (unl s (unr s (unl d unz)))

  -- Task 2.2
  example : unshuffle (cons h (cons s (cons s (cons d nil))))
                      (cons s (cons d nil))
                      (cons h (cons s nil)) :=
  unr h (unr s (unl s (unl d unz)))

  -- Task 2.3
  example : ∀ s₁, ∃ s₂, ∃ s₃, unshuffle s₁ s₂ s₃ :=
  λ s₁,
    stack.induction_on s₁
    (exists.intro nil (exists.intro nil unz))
    (take c : card,
     take t₁ : stack,
     take H : ∃ t₂, ∃ t₃, unshuffle t₁ t₂ t₃,
     obtain t₂ H', from H,
     obtain t₃ H'', from H',
     exists.intro (cons c t₂) (exists.intro t₃ (unl c H'')))

end shuffling
