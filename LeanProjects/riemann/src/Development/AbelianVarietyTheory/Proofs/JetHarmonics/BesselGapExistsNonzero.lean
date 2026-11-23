import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionalSideGrowth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapIntegrabilityStatement

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselShape

theorem bessel_shape : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0) → ∃ (l₀ La : R.H → Wp), IsBes R z π l₀ ∧ NzOn R l₀ ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v = (innerSL ℂ (La v)).smulRight (l₀ w) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hG hOK hS hne
  obtain ⟨w₀, hw₀, v₀, hv₀, hne⟩ := hne
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v₀ ξ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (ContinuousLinearMap.ext hcon)
  have hB := GlobalTheory.T.isBes_bessel_integral_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hG hOK hS
  have hnz : NzOn R (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ ξ₀) := ⟨w₀, hw₀, hξ₀⟩
  set y₀ := be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v₀ ξ₀ with hy₀
  have hyy : ⟪y₀, y₀⟫_ℂ ≠ 0 := fun h0 => hξ₀ (inner_self_eq_zero.mp h0)
  refine ⟨fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ ξ₀,
    fun v => (starRingEnd ℂ (⟪y₀, y₀⟫_ℂ)⁻¹) •
      ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v) y₀,
    hB v₀ hv₀ ξ₀, hnz, ?_⟩
  intro w hw v hv
  ext ξ
  obtain ⟨c, hc⟩ := GlobalTheory.BesselLine.bessel_line hH k r ε mu R Wp z π u μW μN μG νq _ _ hDS hS
    (hB v₀ hv₀ ξ₀) hnz (hB v hv ξ)
  have h1 := hc w hw
  have h2 := hc w₀ hw₀
  rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, h2, h1, ← hy₀, inner_smul_right, Complex.conj_conj]
  congr 1
  field_simp

end GlobalTheory.BesselShape
