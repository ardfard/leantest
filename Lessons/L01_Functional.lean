/-
# Lesson 1 — Lean 4 as a functional programming language

Goal: get fluent in the syntax before we touch proofs. You know FP already,
so this is mostly a dictionary from what you know to how Lean spells it.

How to work: open this file in your editor with the Lean extension running.
Put your cursor on a line and the InfoView (right-hand panel) shows you what
Lean knows there. That panel is the whole game — you will live in it.

Exercises are marked `TODO`. Replace `sorry` with a real definition.
`sorry` type-checks anything and produces a warning, so the file always loads.
-/

/- ## 1. Definitions and types -/

def double (n : Nat) : Nat := 2 * n

-- `#eval` runs it, `#check` shows the type. Look at the InfoView.
#eval double 21
#check double

-- Type ascription and lambdas. `fun x => e` or `fun x ↦ e` (both work).
#check (fun (n : Nat) => n + 1)
#eval (fun n => n + 1) 41

-- Currying is the default; `Nat → Nat → Nat` is `Nat → (Nat → Nat)`.
def add3 (a b c : Nat) : Nat := a + b + c
#check add3 1        -- partially applied: Nat → Nat → Nat

/- ## 2. Inductive types and pattern matching -/

inductive Color where
  | red
  | green
  | blue
  deriving Repr, DecidableEq

open Color

def isWarm : Color → Bool
  | red   => true
  | green => false
  | blue  => false

#eval isWarm red

-- Polymorphic types. `Type` is the universe of ordinary types.
inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (v : α) (r : Tree α)
  deriving Repr

-- Recursion: Lean checks termination. Structural recursion just works.
def Tree.size {α : Type} : Tree α → Nat
  | .leaf       => 0
  | .node l _ r => l.size + 1 + r.size

-- `.leaf` is dot-notation for `Tree.leaf`; Lean infers the namespace from
-- the expected type. You will see this everywhere.
def example1 : Tree Nat :=
  .node (.node .leaf 1 .leaf) 2 .leaf

#eval example1.size

/- TODO 2a: depth of a tree (leaf = 0, node = 1 + max of children). -/
def Tree.depth {α : Type} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => max l.depth r.depth + 1

/- TODO 2b: in-order traversal to a list. `++` appends. -/
def Tree.toList {α : Type} : Tree α → List α
  | .leaf => []
  | .node l v r => l.toList ++ [v] ++ r.toList

/- TODO 2c: map over a tree. -/
def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | .leaf => .leaf
  | .node l v r => .node (l.map f) (f v) (r.map f)


/- ## 3. Structures -/

structure Point where
  x : Float
  y : Float
  deriving Repr

def origin : Point := { x := 0, y := 0 }
def p1 : Point := ⟨3, 4⟩          -- ⟨⟩ is the anonymous constructor

#eval p1.x
#eval { p1 with y := 10 }          -- record update

def Point.norm (p : Point) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

#eval p1.norm                      -- dot notation dispatches on the type

/- ## 4. Type classes -/

class Describable (α : Type) where
  describe : α → String

instance : Describable Color where
  describe
    | red => "warm red"
    | green => "cool green"
    | blue => "cool blue"

#eval Describable.describe blue

-- Instances can depend on other instances.
instance [Describable α ] : Describable (List α) where
  describe xs := String.intercalate ", " (xs.map Describable.describe)

#eval Describable.describe [red, blue]

/- TODO 4a: give `Point` a `Describable` instance printing "(x, y)".
   `toString` works on Float. -/

instance : Describable Point where
  describe p := "(" ++ p.x.toString ++ ", " ++ p.y.toString ++ ")"

#eval Describable.describe p1

/- ## 5. Option, and the do-notation you already know -/

def Tree.first {α : Type} : Tree α → Option α
  | .leaf => none
  | .node .leaf v _ => some v
  | .node l _ _ => l.first

#eval example1.first

-- Monadic do-blocks work like Haskell's.
def addFirsts (t1 t2 : Tree Nat) : Option Nat := do
  let a ← t1.first
  let b ← t2.first
  return a + b

#eval addFirsts example1 example1

/- TODO 5a: safe division returning `Option Float`; `none` when divisor is 0.
   Float equality: `d == 0`. -/
def safeDiv (n d : Float) : Option Float :=
  if d == 0 then none else some (n/d)

/- ## 6. Where this is going

Notice that everything above is an ordinary programming language. The twist
comes in Lesson 2: in Lean, *propositions are types* and *proofs are terms*.
`Tree.size t = t.toList.length` is a type, and a proof of it is a value of
that type. You already know how to build values. That is the whole trick.

Preview — this is a function, and also a proof:
-/

example : ∀ n : Nat, n + 0 = n := fun _ => rfl

-- `rfl` is the constructor of `Eq`. That's it. It's a value.
#check @rfl
