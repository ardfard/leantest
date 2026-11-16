# Learning Lean 4

## Setup (done)

- `elan` 4.2.4, Lean 4.34.1, Lake 5.0.0
- Lake project `leantest` with Mathlib (`v4.34.1`) as a dependency
- Lessons live in `Lessons/`

## Editor — do this first

You have Cursor. Install the **Lean 4** extension (`leanprover.lean4`) from the
extension marketplace, then open this folder. Without it you get no InfoView,
and the InfoView *is* the interface to Lean — it shows the proof state at your
cursor. Writing Lean without it is like debugging without a stack trace.

Check it works: open `Lessons/L01_Functional.lean`, click on a `#eval` line,
and confirm the right-hand panel shows output.

## Checking a file from the terminal

```
lake env lean Lessons/L01_Functional.lean
```

Prints `#eval`/`#check` output plus any errors. Slower than the editor but
useful for a clean pass.

## Roadmap

1. **Functional Lean** — syntax, inductive types, pattern matching, type classes.
   No proofs yet. (`L01_Functional.lean`)
2. **Propositions as types** — Curry-Howard, term-mode proofs, `Prop` vs `Type`.
3. **Tactic mode** — `intro`, `apply`, `exact`, `rw`, `simp`, `induction`.
4. **Proving things about your own code** — the payoff: `Tree.size t = t.toList.length`.
5. **Mathlib** — finding lemmas, `exact?`, `apply?`, `simp?`, algebraic hierarchy.
6. **Real math** — pick a target and formalize it.

## Reference

- Theorem Proving in Lean 4: https://leanprover.github.io/theorem_proving_in_lean4/
- Functional Programming in Lean: https://lean-lang.org/functional_programming_in_lean/
- Mathlib search: https://leansearch.net and https://loogle.lean-lang.org
- Zulip (where the community actually is): https://leanprover.zulipchat.com
