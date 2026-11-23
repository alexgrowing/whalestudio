import Mathlib

theorem UpperTheory.ConvolutionTheory.K.commProj :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (V : Submodule ℂ H) [V.HasOrthogonalProjection]
      (U : H →L[ℂ] H), (∀ v ∈ V, U v ∈ V) → (∀ v ∈ V, ContinuousLinearMap.adjoint U v ∈ V) →
      U ∘L V.starProjection = V.starProjection ∘L U := by
  intro H _ _ _ V _ U h1 h2
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact h1 _ (V.starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
    exact Submodule.starProjection_inner_eq_zero x _ (h2 w hw)
