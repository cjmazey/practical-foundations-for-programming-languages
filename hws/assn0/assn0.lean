/- 15-312 Principles of Programming Languages
 - Assignment 0: Rule Induction
 -/

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
