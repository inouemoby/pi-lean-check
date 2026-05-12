# pi-lean-check

Formal verification for [pi coding agent](https://github.com/earendil-works/pi-mono) using Lean 4. Auto-downloads the Lean theorem prover on first use — no manual setup required. LLMs can call `lean_check` to verify logical reasoning, mathematical proofs, and program correctness with 100% machine-checked certainty.

## Install

```bash
pi install git:github.com/inouemoby/pi-lean-check
```

On first use, Lean 4 (~754MB) is downloaded and cached automatically. All subsequent calls are instant.

## Tools

| Tool | Description |
|------|-------------|
| `lean_check` | Compile and verify Lean 4 proofs. Returns `valid` + errors with exact line/column. |

## Skills

Three built-in skill files teach the LLM how to use Lean:

| Skill | Focus | Examples |
|-------|-------|----------|
| **lean-logic** | Propositional & predicate logic | Modus ponens, De Morgan, quantifier reasoning, case analysis |
| **lean-math** | Arithmetic, induction, number theory | Sum formulas, divisibility, GCD, Fibonacci, inequalities |
| **lean-verification** | Program correctness & invariants | Loop invariants, BST properties, sorting correctness, state machines |

## Usage

LLM calls `lean_check` with Lean 4 code:

```lean
example : 1 + 1 = 2 := by
  native_decide

example (A B : Prop) (h : A ∧ B) : B ∧ A := by
  rcases h with ⟨ha, hb⟩
  exact ⟨hb, ha⟩
```

Response:
- `✓` — proof valid, logically correct
- `✗` — errors with exact line:column locations

## Commands

| Command | Description |
|---------|-------------|
| `/lean-status` | Check if Lean 4 is cached and working |

## What's Available

- **Init library**: propositional logic, predicates, equality, Nat, Int, List, Option
- **Tactics**: `native_decide`, `omega`, `ring`, `simp`, induction, case analysis
- **No Mathlib** (not bundled)

## Limitations

- ~754MB one-time download on first use
- No real numbers, analysis, or advanced algebra (no Mathlib)
- Proofs must fit within Lean's compile limits

## License

MIT
