import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LimV

theorem finiteDimensional_prodSpan_of_fd : ∀ {A B : Type} (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)),
    FiniteDimensional ℂ U₁ → FiniteDimensional ℂ U₂ → FiniteDimensional ℂ (prodSpan U₁ U₂) := by
  intro A B U₁ U₂ h₁ h₂
  let φ : U₁ →ₗ[ℂ] U₂ →ₗ[ℂ] (A × B → ℂ) :=
    LinearMap.mk₂ ℂ (fun a b x => a.1 x.1 * b.1 x.2)
      (fun a a' b => by ext x; simp [add_mul])
      (fun c a b => by ext x; simp [mul_assoc])
      (fun a b b' => by ext x; simp [mul_add])
      (fun c a b => by ext x; simp [mul_left_comm])
  let T : U₁ ⊗[ℂ] U₂ →ₗ[ℂ] (A × B → ℂ) := TensorProduct.lift φ
  have hle : prodSpan U₁ U₂ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro F ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩ : U₁) ⊗ₜ[ℂ] (⟨b, hb⟩ : U₂), by simp [T, φ]⟩
  haveI : FiniteDimensional ℂ (LinearMap.range T) := LinearMap.finiteDimensional_range T
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CompanionTheory.LimV

end
