import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2

theorem UpperTheory.Zero.ConvolutionTheory.EB.powNorm :
    UpperTheory.Zero.ConvolutionTheory.EB.PowNorm := by
  intro H _ _ Q U ρ hQ hU k
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hU
  have hb : ∀ f ∈ Q, ‖U f‖ ≤ ρ * ‖f‖ := by
    intro f hf
    exact (U ∘L Q.subtypeL).le_of_opNorm_le hU ⟨f, hf⟩
  have key : ∀ k : ℕ, ∀ f ∈ Q, (U ^ k) f ∈ Q ∧ ‖(U ^ k) f‖ ≤ ρ ^ k * ‖f‖ := by
    intro k
    induction k with
    | zero =>
      intro f hf
      simp [hf]
    | succ k ih =>
      intro f hf
      obtain ⟨h1, h2⟩ := ih f hf
      have e : (U ^ (k + 1)) f = U ((U ^ k) f) := by
        rw [pow_succ']
        rfl
      rw [e]
      refine ⟨hQ _ h1, (hb _ h1).trans ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 hρ
  refine ⟨fun f hf => (key k f hf).1, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg hρ k) fun q => ?_
  exact (key k q q.2).2
