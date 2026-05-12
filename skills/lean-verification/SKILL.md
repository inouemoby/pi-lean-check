---
name: lean-verification
description: Verify program correctness with the Lean 4 theorem prover via lean_check tool. Use for loop invariants, data structure properties (BST, heaps), sorting algorithm correctness, state machine safety/liveness, termination proofs, memory safety, and behavioral equivalence of implementations.
---

# Lean Program Verification

Use the `lean_check` tool to verify program correctness, algorithmic invariants, and functional specifications using Lean 4. This treats your code as formal mathematical objects and checks that your reasoning about them is logically watertight.

## When to Use

- Verifying that a loop invariant holds through all iterations
- Checking that a recursive function satisfies its specification
- Proving that a sorting algorithm actually sorts
- Validating that refactored code is behaviorally equivalent
- Confirming that an optimization doesn't change semantics
- Proving memory safety or bounds safety properties
- Verifying data structure invariants (e.g., BST property)
- Checking that a mathematical model of a system is consistent
- Proving termination of a recursive or iterative algorithm

## Modeling Programs in Lean

### Pure Functions
```lean
-- Model a function mathematically
def sumTo (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n+1 => (n+1) + sumTo n

-- Verify it satisfies the closed form
example (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  induction n with
  | zero => native_decide
  | succ n ih =>
    simp [sumTo]
    rw [ih]
    -- n*(n+1)/2 + (n+1) = (n+1)*(n+2)/2
    omega
```

### Proving Equivalence of Implementations
```lean
-- Two ways to compute factorial
def factRec : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factRec n

def factIter : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => factIter n ((n+1) * acc)

def factIter' (n : Nat) : Nat := factIter n 1

-- Prove they compute the same thing
example (n : Nat) : factIter' n = factRec n := by
  induction n generalizing factRec with
  | zero => rfl
  | succ n ih =>
    simp [factIter', factIter, factRec]
    -- Show: factIter n ((n+1)*1) = (n+1) * factRec n
    -- We need a lemma about factIter
    sorry -- This requires a stronger invariant
```

## Loop Invariants

Model loops as recursive functions and prove invariants by induction:

```lean
-- Binary search invariant: if x is in array, it's between lo and hi
def inRange (arr : List Nat) (x lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i ≤ hi → i < arr.length → arr.get? i = some x

-- After each step, the invariant holds
example (arr : List Nat) (x lo hi mid : Nat) 
    (hRange : inRange arr x lo hi) (hMid : lo ≤ mid) (hMid' : mid ≤ hi) : True := by
  -- This is where you'd verify each iteration preserves the invariant
  trivial

-- General pattern:
-- 1. State the invariant as a property P(state)
-- 2. Prove P(initial) — base case
-- 3. Prove P(state) → P(next(state)) — inductive step
-- 4. Conclude P(final) — the invariant implies correctness
```

## Data Structure Invariants

```lean
-- Binary Search Tree invariant
inductive Tree (α : Type) where
  | leaf
  | node (left : Tree α) (val : α) (right : Tree α)

def BST (t : Tree Nat) (lo hi : Nat) : Prop :=
  match t with
  | .leaf => True
  | .node l v r => 
    lo ≤ v ∧ v ≤ hi ∧ BST l lo v ∧ BST r v hi

-- Insert preserves BST
def insert (t : Tree Nat) (x : Nat) : Tree Nat :=
  match t with
  | .leaf => .node .leaf x .leaf
  | .node l v r =>
    if x ≤ v then .node (insert l x) v r
    else .node l v (insert r x)

-- The invariant: if input is BST in [lo, hi] and lo ≤ x ≤ hi, output is BST
-- (Requires induction - this is the pattern you'd verify)
```

## Sorting Correctness

```lean
-- Specification: output is sorted and a permutation of input
def Sorted : List Nat → Prop
  | [] => True
  | [_] => True
  | x::y::xs => x ≤ y ∧ Sorted (y::xs)

def Permutation (xs ys : List Nat) : Prop :=
  ∀ x, count x xs = count x ys

-- Insertion sort
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y::ys => if x ≤ y then x::y::ys else y :: insertSorted x ys

def insertionSort : List Nat → List Nat
  | [] => []
  | x::xs => insertSorted x (insertionSort xs)

-- Claim: insertionSort produces a sorted permutation
-- example (xs : List Nat) : Sorted (insertionSort xs) ∧ Permutation xs (insertionSort xs) := by
--   (proof by induction, verifying each lemma)
```

## State Machine Verification

```lean
-- Model a traffic light as a state machine
inductive LightState where
  | red | yellow | green

def nextState : LightState → LightState
  | .red => .green
  | .yellow => .red
  | .green => .yellow

-- Safety property: never goes yellow → yellow
example (s : LightState) : nextState (nextState (nextState s)) = s := by
  cases s <;> rfl

-- Invariant: exactly one light is "active" at a time
-- (For a 3-light intersection, this prevents conflicting greens)
```

## Proving Termination

```lean
-- A decreasing measure proves termination
def ack : Nat → Nat → Nat
  | 0, n => n+1
  | m+1, 0 => ack m 1
  | m+1, n+1 => ack m (ack (m+1) n)
termination_by m n => (m, n)

-- Lean automatically checks the measure decreases each recursive call
-- For complex termination proofs, use `termination_by` with a custom measure
```

## Memory Safety Patterns

```lean
-- Array bounds checking
def safeGet (arr : Array Nat) (i : Nat) (h : i < arr.size) : Nat :=
  arr.get ⟨i, h⟩

-- The proof `h` guarantees no out-of-bounds access
example (arr : Array Nat) (i : Nat) (h : i < arr.size) : safeGet arr i h = arr.get ⟨i, h⟩ := by
  rfl

-- Pattern: Use dependent types to encode preconditions as proof arguments
```

## Relational Reasoning

```lean
-- Proving two programs are equivalent under an abstraction relation
def programA (x : Nat) : Nat := 2*x + 1
def programB (x : Nat) : Nat := (x + x) + 1

example (x : Nat) : programA x = programB x := by
  simp [programA, programB]
  omega

-- Proving an optimization preserves semantics
def slowVersion (xs : List Nat) : Nat :=
  (xs.map (·*2)).sum

def fastVersion (xs : List Nat) : Nat :=
  2 * xs.sum

example (xs : List Nat) : slowVersion xs = fastVersion xs := by
  induction xs with
  | nil => simp [slowVersion, fastVersion]
  | cons x xs ih =>
    simp [slowVersion, fastVersion, List.map_cons, List.sum_cons]
    omega
```

## Verification Strategy

1. **Model** — Express the program/algorithm as a pure mathematical function
2. **Specify** — State the correctness property as a Lean proposition
3. **Simplify** — Break complex properties into smaller lemmas
4. **Inductive cases** — Match on the data structure or iteration count
5. **Invariants** — Find the property that holds at each step/iteration
6. **Automate** — Use `native_decide`/`omega` for arithmetic subgoals

## Common Patterns

| Pattern | Lean Approach |
|---------|---------------|
| Loop invariant | Induction on iteration count |
| Recursive correctness | Structural induction |
| Data structure invariant | Inductive predicate on the type |
| Behavioral equivalence | Prove equal outputs for all inputs |
| No crashes/UB | Dependent types with proof preconditions |
| Termination | `termination_by` with decreasing measure |
| State reachability | Reachability relation + induction |
| Refinement | Simulation relation between abstract and concrete |

## Interpreting Verification Results

If valid:
- Your program satisfies its specification for ALL possible inputs
- The invariant truly holds in every state
- No edge case violates your assumptions

If invalid:
- Lean finds a concrete counterexample in your reasoning
- The error pinpoints which step of your proof fails
- This often reveals a real bug in the algorithm, not just a proof error

## Limitations

- You can only model functional/pure behavior (no IO, no mutable state except via monads)
- Performance properties (time complexity) cannot be verified
- Probabilistic algorithms cannot be verified
- Concurrency is difficult to model without advanced libraries
- Large programs may produce proofs too long for the LLM context window
