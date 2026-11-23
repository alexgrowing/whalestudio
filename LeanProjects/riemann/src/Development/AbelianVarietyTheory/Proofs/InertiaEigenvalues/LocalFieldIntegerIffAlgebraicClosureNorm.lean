import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.Examples
import GroundTheory.LocalFields.Integers
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

noncomputable section

namespace GlobalTheory.PMon.Ram

theorem padic_mem_integer_iff (l : ℕ) [Fact l.Prime] (a : ℚ_[l]) : a ∈ 𝒪[ℚ_[l]] ↔ ‖a‖ ≤ 1 := by
  change valuation ℚ_[l] a ≤ 1 ↔ _
  rw [← map_one (valuation ℚ_[l]), ← (valuation ℚ_[l]).vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]

theorem isIntegral_integer_iff_norm_le (l : ℕ) [Fact l.Prime] (y : Om l) :
    IsIntegral 𝒪[ℚ_[l]] y ↔ ‖y‖ ≤ 1 := by
  have hy : IsIntegral ℚ_[l] y := Algebra.IsIntegral.isIntegral y
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hy)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact (padic_mem_integer_iff l _).1 ((minpoly 𝒪[ℚ_[l]] y).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] y ∈ Polynomial.lifts (algebraMap 𝒪[ℚ_[l]] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, (padic_mem_integer_iff l _).2 (h n)⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hy)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

end GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt (l : ℕ) [Fact l.Prime] (L : Type) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L]
    [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)]
    [IsScalarTower ℚ_[l] L (Om l)] (x : L) :
    (x ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) x‖ ≤ 1) ∧ (valuation L x < 1 ↔ ‖algebraMap L (Om l) x‖ < 1) := by
  have key : ∀ z : L, z ∈ 𝒪[L] ↔ ‖algebraMap L (Om l) z‖ ≤ 1 := by
    intro z
    let f : L →ₐ[𝒪[ℚ_[l]]] Om l := (IsScalarTower.toAlgHom ℚ_[l] L (Om l)).restrictScalars 𝒪[ℚ_[l]]
    have hf : Function.Injective f := (algebraMap L (Om l)).injective
    rw [← isIntegral_integer_iff_norm_le]
    change valuation L z ≤ 1 ↔ IsIntegral 𝒪[ℚ_[l]] (f z)
    rw [isIntegral_algHom_iff f hf, GroundTheory.LocalField.isIntegral_iff ℚ_[l] L z]
  refine ⟨key x, ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hy : algebraMap L (Om l) x ≠ 0 := (map_ne_zero _).2 hx
  have hv : valuation L x ≠ 0 := by simpa using hx
  have h1 := key x⁻¹
  rw [map_inv₀, norm_inv, inv_le_one₀ (norm_pos_iff.2 hy)] at h1
  change valuation L x⁻¹ ≤ 1 ↔ _ at h1
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hv)] at h1
  rw [← not_le, ← not_le, h1]

end GlobalTheory.PMon.Ram

end
