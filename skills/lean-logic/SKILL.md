# lean-logic

Use the `lean_check` tool to formally verify logical reasoning with the Lean 4 theorem prover. This gives 100% machine-checked certainty that a logical deduction is correct.

## When to Use

- You need to verify that a logical implication holds (if A then B)
- You are making a multi-step deductive argument and want to check it
- You are unsure whether a logical equivalence is valid
- You want to ensure a counterexample does NOT exist
- The user asks you to prove something formally
- You are refactoring complex conditional logic and want to verify equivalence

## Lean Basics

### Core Syntax
```lean
-- Propositions are type `Prop`
variables (A B C : Prop)

-- Implication: A → B
-- Conjunction: A ∧ B  
-- Disjunction: A ∨ B
-- Negation: ¬A  (equivalent to A → False)
-- Equivalence: A ↔ B  (equivalent to (A → B) ∧ (B → A))
-- Forall: ∀ x, P x
-- Exists: ∃ x, P x
-- Equality: a = b
-- True / False: `True` and `False` propositions
```

### Proving an `example`
```lean
-- Template:
example : <proposition> := by
  <tactic proof>

-- Each `example` is one independent claim to verify.
-- You can write multiple examples in one code block.
```

### Essential Tactics

| Tactic | Use |
|--------|-----|
| `intro h` | Assume the premise, name it `h` |
| `apply h` | Use a hypothesis `h : A → B` to reduce goal to proving `A` |
| `exact h` | The hypothesis `h` exactly matches the goal |
| `rcases h with ⟨h1, h2⟩` | Destruct `h : A ∧ B` into `h1: A` and `h2: B` |
| `left` / `right` | Prove left/right side of a disjunction `A ∨ B` |
| `constructor` | Split a conjunction goal `A ∧ B` into two subgoals |
| `have h : A := by ...` | Prove an intermediate lemma |
| `apply False.elim` | From `False`, prove anything |
| `refl` | Prove `x = x` |
| `rw [h]` | Rewrite using an equality `h : a = b` |
| `simp` | Simplify using known lemmas |
| `exfalso` | Change goal to `False` (proof by contradiction) |

### Proof Patterns

**Modus Ponens (A → B, A ⊢ B)**
```lean
example (hAB : A → B) (hA : A) : B := by
  apply hAB
  exact hA
```

**Transitivity (A → B, B → C ⊢ A → C)**
```lean
example (hAB : A → B) (hBC : B → C) : A → C := by
  intro hA
  apply hBC
  apply hAB
  exact hA
```

**Commutativity of ∧**
```lean
example (h : A ∧ B) : B ∧ A := by
  rcases h with ⟨ha, hb⟩
  exact ⟨hb, ha⟩
```

**Proof by Contradiction**
```lean
example (h : A) : ¬¬A := by
  intro hnA
  apply hnA
  exact h
```

**De Morgan: ¬(A ∨ B) → ¬A ∧ ¬B**
```lean
example (h : ¬(A ∨ B)) : ¬A ∧ ¬B := by
  constructor
  · intro hA
    apply h
    left
    exact hA
  · intro hB
    apply h
    right
    exact hB
```

**Case Analysis on Disjunction**
```lean
example (h : A ∨ B) (hA : A → C) (hB : B → C) : C := by
  rcases h with (ha | hb)
  · apply hA; exact ha
  · apply hB; exact hb
```

### Quantifiers
```lean
-- Universal: ∀ x, P x
example : ∀ x : Nat, x = x := by
  intro x
  rfl

-- Existential: ∃ x, P x
example : ∃ x : Nat, x = 0 := by
  refine ⟨0, ?_⟩
  rfl

-- Combining quantifiers
example (h : ∀ x, P x → Q x) (hp : P a) : Q a := by
  apply h
  exact hp
```

## Reading Errors

Lean errors are precise. Each error shows:
- **Line:Column** — exact location of the problem
- **Error message** — what went wrong

Common errors:
- `unsolved goals` — you left a subgoal unproven
- `type mismatch` — the expression doesn't match what's expected
- `unknown identifier` — the variable/lemma name doesn't exist
- `tactic failed` — the tactic can't be applied in this context

When a proof fails:
1. Read the error line:column
2. Check what the goal is at that point
3. Fix the specific step, not the whole proof

## Multi-step Reasoning Pattern

For complex reasoning, break it down:
```lean
-- First, prove a helper lemma
lemma helper (h : A ∧ B) : B := by
  rcases h with ⟨_, hb⟩
  exact hb

-- Then use it in the main proof
example (h : A ∧ B) : B ∨ C := by
  left
  apply helper
  exact h
```

## What Init Provides

Lean's Init library is always available. It provides:
- **Propositional logic**: `∧`, `∨`, `→`, `¬`, `↔`
- **Predicates**: `∀`, `∃`
- **Equality**: `=`
- **Natural numbers**: `Nat` (0, 1, 2, ...)
- **Integers**: `Int`
- **Lists**: `List α`
- **Options**: `Option α` (`none`, `some x`)
- **Booleans**: `Bool` (`true`, `false`) — distinct from `Prop`!

## Limitations

- You CANNOT import Mathlib (not bundled). Only Init is available.
- Tactics are limited to those in core Lean 4.
- `native_decide` works for decidable propositions on `Nat`, `Int`, `Fin`.
- `omega` tactic is available for linear arithmetic.
- You can define your own inductive types and recursive functions.

## Best Practices

1. **Start simple**: Verify the simplest version of a claim first
2. **Build up**: Prove lemmas, then compose them
3. **Be explicit**: Name hypotheses clearly (`hAB` for `A → B`)
4. **Use bullets**: `·` for subgoals makes structure clear
5. **Test edge cases**: If you prove `∀ n, ...`, also check `n=0`, `n=1`
6. **When stuck**: Try `simp` to simplify, or `apply` to change the goal
