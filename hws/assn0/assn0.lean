/- 15-312 Principles of Programming Languages
 - Assignment 0: Rule Induction
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

/- Task 2.5 -/
section
  open card stack stack.seperate

  example : ∀ s₁, ∃! s₂ s₃, seperate s₁ s₂ s₃ := sorry
end
