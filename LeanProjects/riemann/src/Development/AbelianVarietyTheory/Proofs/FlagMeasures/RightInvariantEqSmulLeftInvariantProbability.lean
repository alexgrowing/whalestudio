import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem right_inv_eq_smul_left_inv :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (K : Set G) (μ ν : Measure G) [SFinite μ] [SFinite ν], μ Kᶜ = 0 → ν Kᶜ = 0 → μ Set.univ = 1 → (∀ k ∈ K, μ.map (fun g => k * g) = μ) → (∀ k ∈ K, ν.map (fun g => g * k) = ν) → ν = ν Set.univ • μ := by
  intro G _ _ _ K μ ν _ _ hμK hνK hμ1 hμinv hνinv
  ext A hA

  have hS : MeasurableSet {p : G × G | p.1 * p.2 ∈ A} := measurable_mul hA
  have hμae : ∀ᵐ g ∂μ, g ∈ K := by
    rw [ae_iff]
    exact hμK
  have hνae : ∀ᵐ g ∂ν, g ∈ K := by
    rw [ae_iff]
    exact hνK
  have h1 : (ν.prod μ) {p : G × G | p.1 * p.2 ∈ A} = ν Set.univ * μ A := by
    rw [Measure.prod_apply hS]
    have hc : ∀ᵐ h ∂ν, μ (Prod.mk h ⁻¹' {p : G × G | p.1 * p.2 ∈ A}) = μ A := by
      filter_upwards [hνae] with h hh
      show μ ((fun g => h * g) ⁻¹' A) = μ A
      rw [← Measure.map_apply (measurable_const_mul h) hA, hμinv h hh]
    rw [lintegral_congr_ae hc, lintegral_const, mul_comm]
  have h2 : (ν.prod μ) {p : G × G | p.1 * p.2 ∈ A} = ν A := by
    rw [Measure.prod_apply_symm hS]
    have hc : ∀ᵐ g ∂μ, ν ((fun h => (h, g)) ⁻¹' {p : G × G | p.1 * p.2 ∈ A}) = ν A := by
      filter_upwards [hμae] with g hg
      show ν ((fun h => h * g) ⁻¹' A) = ν A
      rw [← Measure.map_apply (measurable_mul_const g) hA, hνinv g hg]
    rw [lintegral_congr_ae hc, lintegral_const, hμ1, mul_one]
  rw [Measure.smul_apply, smul_eq_mul, ← h1, h2]

end GlobalTheory.IwConst
