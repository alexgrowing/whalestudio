import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolution

namespace ReciprocityTheory.L2DbarEstimates

open scoped InnerProductSpace

theorem ontoWithBound (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] :
    OntoWithBoundStatement E H₁ H₂ := by
  intro G Gs θ Q c hc hadj hbd f hf
  let θ' : (Q × E) →ₗ[ℂ] H₁ := Gs ∘ₗ Q.subtype ∘ₗ LinearMap.fst ℂ Q E + θ ∘ₗ LinearMap.snd ℂ Q E
  let ℓ : (Q × E) →ₗ[ℂ] ℂ := (innerₛₗ ℂ f) ∘ₗ Q.subtype ∘ₗ LinearMap.fst ℂ Q E
  have hθ' : ∀ x : Q × E, θ' x = Gs x.1 + θ x.2 := fun x => rfl
  have hℓ : ∀ x : Q × E, ℓ x = ⟪f, (x.1 : H₂)⟫_ℂ := fun x => rfl
  have hA : 0 ≤ ‖f‖ ^ 2 / c := by positivity
  have hbound : ∀ x : Q × E, ‖ℓ x‖ ^ 2 ≤ ‖f‖ ^ 2 / c * ‖θ' x‖ ^ 2 := by
    intro x
    rw [hℓ, hθ']
    have h1 : ‖⟪f, (x.1 : H₂)⟫_ℂ‖ ≤ ‖f‖ * ‖(x.1 : H₂)‖ := norm_inner_le_norm _ _
    have h2 := hbd x.1 x.1.2 x.2
    have h0 : 0 ≤ ‖⟪f, (x.1 : H₂)⟫_ℂ‖ := norm_nonneg _
    calc ‖⟪f, (x.1 : H₂)⟫_ℂ‖ ^ 2 ≤ (‖f‖ * ‖(x.1 : H₂)‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = ‖f‖ ^ 2 / c * (c * ‖(x.1 : H₂)‖ ^ 2) := by
        rw [mul_pow, div_mul_eq_mul_div, eq_div_iff hc.ne']
        ring
      _ ≤ ‖f‖ ^ 2 / c * ‖Gs x.1 + θ x.2‖ ^ 2 := mul_le_mul_of_nonneg_left h2 hA
  obtain ⟨h, -, hnorm, hinner⟩ := rieszOnRange (Q × E) H₁ θ' ℓ _ hA hbound
  refine ⟨h, ?_, ?_, ?_⟩
  · intro u hu
    have hh : ⟪h, Gs u⟫_ℂ = ⟪f, u⟫_ℂ := by simpa [hθ', hℓ] using hinner (⟨u, hu⟩, 0)
    rw [← hadj u hu h, ← inner_conj_symm, hh, inner_conj_symm]
  · intro e
    simpa [hθ', hℓ] using hinner (0, e)
  · rw [le_div_iff₀ hc] at hnorm
    linarith [hnorm]

end ReciprocityTheory.L2DbarEstimates
