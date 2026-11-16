/-
# Lesson 2 — Propositions are types, proofs are terms

No tactics in this lesson. That's deliberate. Tactics are a *scripting layer*
that builds terms for you, and if you meet them before you've seen the terms
they build, they feel like magic incantations. You have FP: you already know
how to build values. So we build proofs by hand, and in Lesson 3 tactics will
look like what they are — automation, not a separate language.
-/

namespace L02

/- ## 1. Prop is a universe, like Type

`Type` is the universe of data. `Prop` is the universe of *statements*.
Both are `Sort`s. The difference is what lives in them.
-/

#check Nat              -- Type
#check (2 + 2 = 4)      -- Prop   ← a statement, not a Bool
#check (2 + 2 = 5)      -- Prop   ← also a Prop. Being false is fine.

-- An *inhabitant* of a Prop is a proof of it.
theorem two_plus_two : 2 + 2 = 4 := rfl
#check two_plus_two     -- 2 + 2 = 4

-- Note what you CANNOT do: there is no term of type `2 + 2 = 5`.
-- "Provable" = "the type is inhabited". That's the entire idea.

/- ## 2. Implication IS the function arrow

`p → q` is literally a function type. A proof of `p → q` is a function
taking a proof of `p` to a proof of `q`. Same arrow, same `fun`.
-/

variable (p q r : Prop)

-- The K combinator. You have written this a hundred times.
theorem const_thm : p → q → p :=
  fun hp => fun _ => hp

-- The S combinator, also known as distribution of implication.
theorem s_thm : (p → q → r) → (p → q) → p → r :=
  fun hpqr => fun hpq => fun hp => hpqr hp (hpq hp)

-- `theorem` and `def` are the same keyword with different defaults.
-- Convention: `theorem` when the type is a Prop, `def` when it's data.

/- TODO 2a: function composition, spelled as implication transitivity. -/
theorem imp_trans : (p → q) → (q → r) → (p → r) :=
  fun hpq => fun qr => fun hp => qr (hpq hp)

/- ## 3. ∀ is the dependent function type

`∀ x : α, P x` is the type of functions taking `x : α` to a proof of `P x`.
The return *type* depends on the argument's *value*. That's all "dependent" means.
-/

theorem refl_all : ∀ n : Nat, n = n :=
  fun _ => rfl

-- In fact `p → q` is just notation for `∀ _ : p, q`. One construct, not two.
#check @const_thm

/- TODO 3a: prove this. `h n` gives you a proof of `P n`. -/
theorem forall_imp {α : Type} (P Q : α → Prop) :
    (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) :=
  sorry

/- ## 4. ∧ is a structure

`And p q` is a one-constructor structure with fields `left` and `right`.
Exactly like `Point`. So `⟨_, _⟩` builds it and `.left` projects out of it.
-/

#print And

theorem and_swap : p ∧ q → q ∧ p :=
  fun h => ⟨h.right, h.left⟩

-- Or with explicit names, if you prefer seeing the machinery:
theorem and_swap' : p ∧ q → q ∧ p :=
  fun h => And.intro (And.right h) (And.left h)

/- TODO 4a: -/
theorem and_assoc' : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  sorry

/- ## 5. ∨ is an inductive type with two constructors

`Or p q` has `Or.inl : p → p ∨ q` and `Or.inr : q → p ∨ q`.
To *build* one, pick a constructor. To *use* one, pattern match — because
you must handle both ways it could have been built.
-/

#print Or

theorem or_swap : p ∨ q → q ∨ p :=
  fun h => match h with
    | .inl hp => .inr hp
    | .inr hq => .inl hq

/- TODO 5a: -/
theorem or_assoc' : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
  sorry

/- ## 6. False, and negation

`False` is the inductive type with NO constructors. Nothing builds it.
`¬p` is *defined* as `p → False`. And `False.elim : False → C` for any `C` —
which is just the eliminator for an empty type, the same `absurd`/`⊥`
you know from Haskell's `Data.Void`.
-/

#print False
#check @False.elim

theorem not_not_intro : p → ¬¬p :=
  fun hp => fun hnp => hnp hp     -- unfold: ¬¬p is (p → False) → False

theorem absurd' : p → ¬p → q :=
  fun hp hnp => False.elim (hnp hp)

/- TODO 6a: one direction of De Morgan. This one is constructively true. -/
theorem not_or : ¬(p ∨ q) → ¬p ∧ ¬q :=
  sorry

/- TODO 6b: contrapositive. -/
theorem mt' : (p → q) → ¬q → ¬p :=
  sorry

/- Note: `¬(p ∧ q) → ¬p ∨ ¬q` is NOT provable here — it needs classical logic
   (`Classical.em`). Lean's core logic is constructive; classical reasoning is
   available but must be invoked explicitly. Try it and watch yourself get stuck;
   that stuckness is informative. -/

/- ## 7. ↔ is a structure holding two functions -/

theorem and_comm_iff : (p ∧ q) ↔ (q ∧ p) :=
  ⟨and_swap p q, and_swap q p⟩

/- TODO 7a: currying, as a logical equivalence. -/
theorem curry_iff : (p ∧ q → r) ↔ (p → q → r) :=
  sorry

/- ## 8. ∃ is a structure: a witness paired with a proof

`Exists P` holds `w : α` together with a proof of `P w`. It is a dependent
pair — the type of the second field depends on the value of the first.
Build with `⟨witness, proof⟩`, destructure by matching.
-/

theorem exists_even : ∃ n : Nat, n + n = 8 :=
  ⟨4, rfl⟩

theorem exists_imp {α : Type} (P Q : α → Prop) :
    (∀ x, P x → Q x) → (∃ x, P x) → (∃ x, Q x) :=
  fun h hex => match hex with
    | ⟨w, hw⟩ => ⟨w, h w hw⟩

/- TODO 8a: swapping an existential past a conjunction. -/
theorem exists_and {α : Type} (P Q : α → Prop) :
    (∃ x, P x ∧ Q x) → (∃ x, P x) :=
  sorry

/- ## 9. Why proofs don't slow your program down

`Prop` is *proof-irrelevant*: any two proofs of the same proposition are
considered equal, and proofs are erased at compile time. That's the real
distinction from `Type` — `Nat` inhabitants matter individually, `p ∧ q`
inhabitants don't. You can carry proofs around in your data structures
for free.
-/

structure PosNat where
  val : Nat
  pos : val > 0      -- a proof, stored in the structure, erased at runtime

def three : PosNat := ⟨3, by decide⟩
#eval three.val

/- ## Next

Every proof above is a term you could have written in any functional
language with dependent types. Lesson 3 introduces tactics, which write
these terms for you — and you'll be able to see exactly what they produced
with `#print`. Try it now on something you just proved:
-/

#print and_swap

end L02
