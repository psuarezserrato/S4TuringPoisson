-- Verified by gemma_loop.py (declaration: S4TuringPoisson.Reversible.encodeInputTape_apply, tier: T0, attempt: 1, spec: Universal.lean)
theorem encodeInputTape_apply (M : FinTM0) (t : FinSupportedTape M) :
    encodeInputTape M t = Tape.mk₁ (encodeInputList M t) :=
  by
  unfold encodeInputTape
  rfl
