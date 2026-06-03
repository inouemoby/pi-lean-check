# pi-lean-check

Formal verification for [pi coding agent](https://github.com/earendil-works/pi-mono) using Lean 4. Use `lean_check` to verify logical reasoning, mathematical proofs, and program correctness with 100% machine-checked certainty.

## Install

```bash
pi install git:github.com/inouemoby/pi-lean-check
```

## Lean 4 Installation

Lean 4 is NOT auto-downloaded. Install before first use:

1. Run `/lean-install` inside pi — downloads from GitHub automatically
2. Or download manually from https://github.com/leanprover/lean4/releases

### Install Location

Extract the zip into the extension's `bin/` directory:

```
~/.pi/agent/extensions/pi-lean-check/bin/lean-<version>-<platform>/bin/lean
```

Examples:

| Platform | Path |
|----------|------|
| Windows | `~/.pi/agent/extensions/pi-lean-check/bin/lean-4.29.1-windows/bin/lean.exe` |
| macOS ARM | `~/.pi/agent/extensions/pi-lean-check/bin/lean-4.29.1-darwin_aarch64/bin/lean` |
| Linux | `~/.pi/agent/extensions/pi-lean-check/bin/lean-4.29.1-linux/bin/lean` |

Use `/lean-status` to verify installation.

## Tools

| Tool | Description |
|------|-------------|
| `lean_check` | Compile and verify Lean 4 proofs. Returns `valid` + errors with exact line/column. |

## Skills

| Skill | Focus | Examples |
|-------|-------|---------|
| **lean-logic** | Propositional & predicate logic | Modus ponens, De Morgan, quantifier reasoning, case analysis |
| **lean-math** | Arithmetic, induction, number theory | Sum formulas, divisibility, GCD, Fibonacci, inequalities |
| **lean-verification** | Program correctness & invariants | Loop invariants, BST properties, sorting correctness, state machines |

## Usage

Call `lean_check` with Lean 4 code:

```lean
example : 1 + 1 = 2 := by
  native_decide

example (A B : Prop) (h : A ∧ B) : B ∧ A := by
  rcases h with ⟨ha, hb⟩
  exact ⟨hb, ha⟩
```

Response:
- `✓` — proof valid, logically correct (warnings shown with line:column)
- `✗` — errors with exact line:column locations and tactic state

## Commands

| Command | Description |
|---------|-------------|
| `/lean-status` | Check if Lean 4 is installed and working |
| `/lean-install` | Download and install Lean 4 (~750MB, one-time) |

## Limitations

- ~750MB one-time download
- No Mathlib (no real numbers, analysis, or advanced algebra)
- Proofs must fit within Lean's compile limits

## License

MIT
