/- 15-312 Principles of Programming Languages
   Assignment 0: Rule Induction
 -/

import standard

/- 2 Shuffling cards -/

inductive card : Type :=
| heart : card
| spade : card
| club : card
| diamond : card

namespace card
  notation `♡` := heart
  notation `♠` := spade
  notation `♣` := club
  notation `♢` := diamond
end card

inductive stack : Type :=
| nil : stack
| cons : card → stack → stack

namespace stack
  notation h :: t  := cons h t
  notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

  inductive unshuffle : stack → stack → stack → Prop :=
  | intro_nil : unshuffle [] [] []
  | intro_right : ∀ {c s₁ s₂ s₃},
                    unshuffle s₁ s₂ s₃ → unshuffle (c :: s₁) s₂ (c :: s₃)
  | intro_left : ∀ {c s₁ s₂ s₃},
                   unshuffle s₁ s₂ s₃ → unshuffle (c :: s₁) (c :: s₂) s₃

  namespace unshuffle
    notation `🂠🂠🂠` := intro_nil
    notation `🂡🂠🂡` := intro_right
    notation `🂡🂡🂠` := intro_left
  end unshuffle
end stack

/- Task 2.1 -/
section
  open card stack stack.unshuffle function

  example : unshuffle [♡, ♠, ♠, ♢] [♠, ♢] [♡, ♠] :=
  🂡🂠🂡 $ 🂡🂡🂠 $ 🂡🂠🂡 $ 🂡🂡🂠 $ 🂠🂠🂠
end

/- Task 2.2 -/
section
  open card stack stack.unshuffle function

  example : unshuffle [♡, ♠, ♠, ♢] [♠, ♢] [♡, ♠] :=
  🂡🂠🂡 $ 🂡🂠🂡 $ 🂡🂡🂠 $ 🂡🂡🂠 $ 🂠🂠🂠
end

/- Task 2.3 -/
section
  open card stack stack.unshuffle

  example : ∀ s₁, ∃ s₂ s₃, unshuffle s₁ s₂ s₃ :=
  take s₁,
  stack.induction_on s₁
  (exists.intro [] (exists.intro [] 🂠🂠🂠))
  (take c s₁' IH,
   obtain s₂ s₃ IH', from IH,
   exists.intro s₂ (exists.intro (c :: s₃) (🂡🂠🂡 IH')))
end

/- Task 2.4 -/
namespace stack
  open card

  inductive seperate : stack → stack → stack → Prop :=
  | intro_nil : seperate [] [] []
  | intro_spade : ∀ {s₁ s₂ s₃},
                    seperate s₁ s₂ s₃ → seperate (♠ :: s₁) s₂ (♠ :: s₃)
  | intro_club : ∀ {s₁ s₂ s₃},
                   seperate s₁ s₂ s₃ → seperate (♣ :: s₁) s₂ (♣ :: s₃)
  | intro_heart : ∀ {s₁ s₂ s₃},
                    seperate s₁ s₂ s₃ → seperate (♡ :: s₁) (♡ :: s₂) s₃
  | intro_diamond : ∀ {s₁ s₂ s₃},
                      seperate s₁ s₂ s₃ → seperate (♢ :: s₁) (♢ :: s₂) s₃
end stack

section
  open card stack stack.seperate function

  example : seperate [♡, ♢, ♠] [♡, ♢] [♠] :=
  intro_heart $ intro_diamond $ intro_spade $ intro_nil

  example : seperate [♠, ♢, ♣, ♡] [♢, ♡] [♠, ♣] :=
  intro_spade $ intro_diamond $ intro_club $ intro_heart $ intro_nil

  example : seperate [♣, ♡, ♣, ♠] [♡] [♣, ♣, ♠] :=
  intro_club $ intro_heart $ intro_club $ intro_spade $ intro_nil

  example : ¬seperate [♡, ♠] [♡, ♠] [] := sorry

  example : ¬seperate [♡, ♢] [♢, ♡] [] := sorry
end

/- Task 2.5

   It means s₁ uniquely determines s₂ and s₃ (and they always exist.)
   "unshuffle" does not have this mode because in its case they are
   not unique (e.g. Task 2.2.)

 -/
section
  open card stack stack.seperate

  example : ∀ s₁, ∃! s₂ s₃, seperate s₁ s₂ s₃ := sorry
end

/- 3 Cutting cards -/

namespace stack
  inductive even : stack → Prop :=
  | nil : even []
  | cons : ∀ c s, odd s → even (c :: s)
  with odd : stack → Prop :=
  | cons : ∀ c s, even s → odd (c :: s)
end stack

/- Task 3.1 -/
section
  open stack

  check @even.induction_on
  check @odd.induction_on
end

/- Task 3.2

   This seems quite impossible?  The following is not exactly a proof.
 -/
namespace stack
  inductive is_a_stack : stack → Prop :=
  | of_course_it_is : ∀ s, is_a_stack s

  example : ∀ s, even s → is_a_stack s := sorry
end stack

/- Task 3.3 -/
namespace stack
  theorem even.induction_even :
      ∀ {S : stack → Prop},
        S [] →
        (∀ c₁ c₂ s, S s → S (c₁ :: c₂ :: s)) →
        ∀ s, even s → S s :=
  λ S IB IH,
    λ s `even s`,
      @even.induction_on (λ s, S s) (λ s, ∀ c, S (c :: s)) s `even s`
        IB
        (λ c s `_` H, H c)
        (λ c₂ s `even s` `S s` c₁, IH c₁ c₂ s `S s`)
end stack

/- Task 3.4 -/
namespace stack
  inductive cut : stack → stack → stack → Prop :=
  | nil : ∀ s, cut s s []
  | cons : ∀ c s₁ s₂ s₃, cut s₁ s₂ s₃ → cut (c :: s₁) s₂ (c :: s₃)

  namespace cut
    premise inversion_nil : ∀ s₁ s₂, cut s₁ s₂ [] → s₁ = s₂
    premise inversion_cons : ∀ c s₁ s₂ s₃,
                               cut s₁ s₂ (c :: s₃) →
                               ∃ s₁', s₁ = (c :: s₁') ∧ cut s₁' s₂ s₃

    example : ∀ s₁ s₂ s₃, even s₂ → even s₃ → cut s₁ s₂ s₃ → even s₁ :=
    have H : ∀ s₃, even s₃ → ∀ s₁ s₂, even s₂ → cut s₁ s₂ s₃ → even s₁, from
      even.induction_even
        (take s₁ s₂,
         assume He₂ Hc,
         have s₁ = s₂, from inversion_nil s₁ s₂ Hc,
         eq.subst (eq.symm this) He₂)
        (take c₁ c₂ s,
         assume IH,
         take s₁ s₂,
         assume He₂ Hc,
         obtain s₁' Es₁', from inversion_cons _ _ _ _ Hc,
         obtain s₁'' Es₁'', from inversion_cons _ _ _ _ (and.right Es₁'),
         have even s₁'', from IH s₁'' s₂ He₂ (and.right Es₁''),
         have s₁ = c₁ :: s₁', from and.left Es₁',
         have s₁' = c₂ :: s₁'', from and.left Es₁'',
         have s₁ = c₁ :: c₂ :: s₁'', from eq.subst `s₁' = c₂ :: s₁''` `s₁ = c₁ :: s₁'`,
         have even (c₁ :: c₂ :: s₁''), from even.cons c₁ _ (odd.cons c₂ s₁'' `even s₁''`),
         eq.subst (eq.symm `s₁ = c₁ :: c₂ :: s₁''`) this),
    λ s₁ s₂ s₃ He₂ He₃, H s₃ He₃ s₁ s₂ He₂
  end cut
end stack
