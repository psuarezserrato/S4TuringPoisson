---
trigger: always_on
description: "Mandatory Lean 4 kernel, axiom, LSP-first, and anti-vacuity invariants for S4TuringPoisson."
---

# S4TuringPoisson Non-Negotiable Formalization Rules

- **Zero Sorry / Zero Custom Axioms**: No merged file may contain `sorry`, `admit`, `axiom`, `unsafe`, or `implemented_by`. Every headline theorem must pass `#print axioms` showing strictly a subset of `{propext, Classical.choice, Quot.sound}`.
- **LSP-First Proof Loop**: Query `lean_goal` and `lean_diagnostic_messages` first, search Mathlib and TauCeti via `lean_local_search` and `lean_loogle` before inventing definitions, and test tactics with `lean_multi_attempt`. Pass `--commit=never` if invoking `autoprove` inside a worker worktree prior to verifier sign-off.
- **Junk-Value Vigilance**: Mathlib's `mfderiv`, `fderiv`, `VectorField.mpullback`, and division by zero evaluate to `0` when differentiability or invertibility hypotheses fail. Every definition or theorem using derivatives or top-form division must carry explicit smoothness/nowhere-vanishing hypotheses and a concrete non-zero `Checks` witness.
- **Anti-Suspension & Anti-Vacuity**:
  - Never prove 4-manifold Turing completeness via topological 3D suspension (`S^3 x (-1,1)`); the diffeomorphism MUST preserve the symplectic foliation and global unimodular volume form of the generically rank-2 Jacobian-Poisson structure `pi_f`.
  - Never allow `IsTuringComplete` to construct `(p, U)` via `Classical.by_cases` on halting: `encodePoint` depends ONLY on `(M, inputTape)` (with computable rational approximations) and `encodeOpen` depends ONLY on `(M, k, targetWindow)` with `U` proved nonempty.
- **Exclusive File Ownership**: Edit only files inside your assigned `S4TuringPoisson/<Subdir>/` boundary. Propose cross-module signature updates to `@coordinator` on the Shared Message Board.
