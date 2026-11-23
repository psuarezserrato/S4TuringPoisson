-- Verified by gemma_loop.py (declaration: S4TuringPoisson.CMPP.tape_mk₁_eq_mk₂_nil, tier: T0, attempt: 1, spec: Simulator.lean)
theorem tape_mk₁_eq_mk₂_nil {Γ : Type*} [Inhabited Γ] (l : List Γ) :
    Tape.mk₁ l = Tape.mk₂ [] l :=
  by
  rfl
