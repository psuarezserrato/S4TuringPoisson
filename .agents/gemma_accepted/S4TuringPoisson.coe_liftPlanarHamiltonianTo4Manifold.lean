-- Verified by gemma_loop.py (declaration: S4TuringPoisson.coe_liftPlanarHamiltonianTo4Manifold, tier: T0, attempt: 1, spec: PoissonHamiltonian.lean)
@[simp]
theorem coe_liftPlanarHamiltonianTo4Manifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [A : AdmitsWrinkledOrBrokenLefschetzFibration M]
    {r₀ : ℝ} (P : CompactlySupportedPlanarHamiltonian r₀) :
    ⇑(liftPlanarHamiltonianTo4Manifold M P) = liftPlanarHamiltonianRaw M P :=
  by
  unfold liftPlanarHamiltonianTo4Manifold
  rcases liftPlanarHamiltonianTo4Manifold M P with ⟨f, hf⟩
  ext x
  rfl
