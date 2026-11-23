import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

open NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic

namespace GlobalTheory.CompanionTheory.RankinSelbergTop

open Ad3 Ad3.R

theorem isUnit1_mul_inv {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) : IsUnit1 (μ₁ * μ₂⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => μ₁ x * (μ₂ x)⁻¹
    exact h₁.1.mul h₂.1.inv
  · show ‖((μ₁ x * (μ₂ x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, h₁.2, h₂.2]; simp

theorem isUnramifiedChar_mul_inv {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnramifiedChar μ₁) (h₂ : IsUnramifiedChar μ₂) : IsUnramifiedChar (μ₁ * μ₂⁻¹) := by
  intro x hx
  have e₁ : μ₁ x = 1 := h₁ hx
  have e₂ : μ₂ x = 1 := h₂ hx
  rw [MonoidHom.mem_ker]
  show μ₁ x * (μ₂ x)⁻¹ = 1
  rw [e₁, e₂]; simp

theorem rs_of (hB : B0) (h0 : F0) (h1 : F1) (h7 : F7) (hX : X1) : RS := by
  intro k N _ hk χ hχ f a hf ha hp
  obtain ⟨ω, hω⟩ := h0 N χ
  obtain ⟨-, φ, hφ⟩ := h1 k N χ f a hf ha.2.1 ω hω
  obtain ⟨μ₁, μ₂, φ₀, hM, hsat⟩ := h7 k N hk χ hχ f a hf ha ω φ hω hφ hp
  have hN : N ≠ 0 := NeZero.ne N
  have hfin : {v : Pl | pOf v ∣ N}.Finite :=
    ((N.divisors : Set ℕ).toFinite.preimage hB.2.1.injOn).subset (fun v hv => by
      simp only [Set.mem_setOf_eq] at hv
      simp [Nat.mem_divisors, hv, hN])
  let D : Dat := ⟨k, hk, fun v => μ₁ v * (μ₂ v)⁻¹, fun v => isUnit1_mul_inv (hM.u₁ v) (hM.u₂ v), hfin.toFinset,
    fun v hv => by
      have hv' : ¬ pOf v ∣ N := by simpa using hv
      obtain ⟨e₁, e₂, -⟩ := hM.good v hv'
      exact isUnramifiedChar_mul_inv e₁ e₂⟩
  have hbad : ∀ v, v ∈ D.bad ↔ pOf v ∣ N := fun v => by simp [D]
  refine ⟨D, rfl, ⟨hbad, fun v hv => ?_⟩, ?_⟩
  · exact hsat v (by rwa [hbad] at hv)
  · exact hX k N hk χ hχ f a hf ha ω φ hω hφ hp μ₁ μ₂ φ₀ hM D rfl (fun v => rfl) hbad

example : B0 → F0 → F1 → F7 → X1 → RS := rs_of

end GlobalTheory.CompanionTheory.RankinSelbergTop
