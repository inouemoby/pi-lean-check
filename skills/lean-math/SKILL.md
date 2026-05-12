# lean-math

Use the `lean_check` tool to verify mathematical theorems, proofs, and calculations using Lean 4. The `native_decide` and `omega` tactics can automatically decide many arithmetic, linear, and combinatorial statements.

## When to Use

- Proving arithmetic identities (e.g., `(a+b)^2 = a^2 + 2ab + b^2`)
- Verifying divisibility or modular arithmetic claims
- Checking inequalities over natural numbers or integers
- Confirming combinatorial identities (sums, products, binomial)
- Validating algebraic manipulations
- Verifying that a formula or recurrence relation holds
- Proving simple number theory results
- Checking that a bound or estimate is correct

## Arithmetic with `native_decide`

`native_decide` is the most powerful tactic for arithmetic. It can decide:

**Natural numbers**:
```lean
example : 123 + 456 = 579 := by native_decide
example : 2^10 = 1024 := by native_decide
example (a b : Nat) : (a + b)^2 = a^2 + 2*a*b + b^2 := by native_decide
```

**Integers**:
```lean
example : (5 : Int) * (-3) = -15 := by native_decide
example (x y : Int) : (x + y)*(x - y) = x^2 - y^2 := by native_decide
```

**Divisibility**:
```lean
example : 6 ∣ 42 := by native_decide
example (n : Nat) (h : n ≤ 100) : n^2 ≤ 10000 := by
  omega
```

**Inequalities with `omega`**:
```lean
-- omega handles linear arithmetic over Nat and Int
example (x y : Nat) (hx : x ≤ 10) (hy : y ≤ 10) : x + y ≤ 20 := by
  omega

example (a b : Int) (h : a ≤ b) : a + 1 ≤ b + 1 := by
  omega
```

## Induction Proofs

For statements that require induction:

```lean
-- Sum of first n numbers: n*(n+1)/2
example (n : Nat) : 2 * (∑ i in Finset.range n, i) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih => 
    simp [Finset.sum_range_succ]
    omega

-- Simple induction: ∀ n, 0 ≤ n
example (n : Nat) : 0 ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => exact Nat.zero_le (Nat.succ n)

-- Power identity: a^m * a^n = a^(m+n)
example (a m n : Nat) : a^m * a^n = a^(m+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, pow_succ, ← mul_assoc, ih, mul_comm (a^m), mul_assoc]
```

## Sets and Functions

```lean
-- Function composition
example (f : α → β) (g : β → γ) (x : α) : (g ∘ f) x = g (f x) := by rfl

-- Injection proof
example {f : Nat → Nat} (h : ∀ a b, f a = f b → a = b) : Function.Injective f := by
  intro a b h_eq
  exact h a b h_eq

-- Surjection proof
example (f : Nat → Nat) (h : ∀ y, ∃ x, f x = y) : Function.Surjective f := by
  intro y
  rcases h y with ⟨x, hx⟩
  exact ⟨x, hx⟩
```

## Working with Lists

```lean
open List

-- Length of append
example (xs ys : List α) : length (xs ++ ys) = length xs + length ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

-- Reverse reverse = identity
example (xs : List α) : reverse (reverse xs) = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [reverse_append, ih]

-- Map preserves length
example (f : α → β) (xs : List α) : length (map f xs) = length xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]
```

## Common Number Theory

```lean
-- Even/Odd
def Even (n : Nat) : Prop := ∃ k, n = 2*k
def Odd (n : Nat) : Prop := ∃ k, n = 2*k + 1

-- Sum of two evens is even
example (a b : Nat) (ha : Even a) (hb : Even b) : Even (a + b) := by
  rcases ha with ⟨k, hk⟩
  rcases hb with ⟨l, hl⟩
  refine ⟨k + l, ?_⟩
  rw [hk, hl]
  ring

-- Product of two odds is odd
example (a b : Nat) (ha : Odd a) (hb : Odd b) : Odd (a * b) := by
  rcases ha with ⟨k, hk⟩
  rcases hb with ⟨l, hl⟩
  refine ⟨2*k*l + k + l, ?_⟩
  rw [hk, hl]
  ring

-- GCD properties (basic)
-- If d ∣ a and d ∣ b, then d ∣ (a + b)
example (d a b : Nat) (hda : d ∣ a) (hdb : d ∣ b) : d ∣ (a + b) := by
  apply Nat.dvd_add hda hdb
```

## Sequences and Recurrences

```lean
-- Fibonacci (first values)
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)

example : fib 5 = 5 := by native_decide
example : fib 10 = 55 := by native_decide

-- Factorial
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

example : fact 5 = 120 := by native_decide
```

## Handling Existentials

```lean
-- There exists a number greater than any given number
example (n : Nat) : ∃ m : Nat, n < m := by
  refine ⟨n+1, ?_⟩
  omega

-- For every x, there exists y such that x*y = 0
example : ∀ x : Nat, ∃ y : Nat, x * y = 0 := by
  intro x
  refine ⟨0, ?_⟩
  simp

-- Between any two distinct integers there's another integer (false!)
example : ¬ (∀ a b : Int, a < b → ∃ c : Int, a < c ∧ c < b) := by
  intro h
  have hcase := h 0 1 (by omega)
  rcases hcase with ⟨c, hc1, hc2⟩
  omega
```

## Proof Strategy

1. **Try `native_decide` first** — it handles most arithmetic and decidable propositions
2. **Use `omega` for inequalities** — linear arithmetic over Nat/Int
3. **`simp` to simplify** — normalizes expressions
4. **`ring` for polynomial identities** — (a+b)^2 = a^2 + 2ab + b^2
5. **Induction** — needed for recursive definitions and ∀n statements
6. **Case analysis** — split on constructors of inductive types

## What's Available vs What's Not

Available:
- `Nat`, `Int`, `Fin n` (numbers modulo n)
- `List α`, `Array α`
- `Option α`
- `Finset α` (finite sets)
- `native_decide`, `omega`, `ring`, `simp`, `arith`
- Induction, case analysis, rewriting
- Basic `Nat` lemmas (`Nat.add_comm`, `Nat.add_assoc`, `Nat.mul_comm`, etc.)

NOT available:
- Real numbers (ℝ, ℚ) — no Mathlib
- Analysis (limits, continuity, derivatives)
- Group theory, ring theory, linear algebra beyond basic arithmetic
- Complex data structures beyond List/Array/Option
- `positivity`, `nlinarith`, `polyrith` (Mathlib tactics)

## Interpreting Results

If `lean_check` returns valid:
- Your statement is 100% logically and mathematically correct
- No counterexample exists
- The proof is machine-verified

If it fails:
- The error tells you exactly which line and column has the problem
- "unsolved goals" — add more proof steps
- "type mismatch" — check your expression types
- "tactic `native_decide` evaluated that ... is false" — the arithmetic statement is genuinely false
