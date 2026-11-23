import Mathlib
import GroundTheory.LocalFields.LocalFourierPadic

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology
open scoped NNReal ENNReal

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

instance borelSpace_units : BorelSpace Kˣ :=
  measurableEmbedding_units_val.borelSpace isOpenEmbedding_units_val.isInducing

def unitsMeasureOf (μ : Measure K) : Measure Kˣ :=
  Measure.comap Units.val (μ.withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹)

def multHaarOf (μ : Measure K) : Measure Kˣ := multHaarConst K • unitsMeasureOf μ

theorem multHaarOf_haarIntegers : multHaarOf (haarIntegers K) = multHaar K := by
  rw [multHaarOf, unitsMeasureOf, multHaar, Measure.comap_smul]

omit [BorelSpace K] in
theorem unitsMeasureOf_smul (c : ℝ≥0∞) (μ : Measure K) :
    unitsMeasureOf (c • μ) = c • unitsMeasureOf μ := by
  rw [unitsMeasureOf, unitsMeasureOf, withDensity_smul_measure, Measure.comap_smul]

omit [BorelSpace K] in
theorem multHaarOf_smul (c : ℝ≥0∞) (μ : Measure K) : multHaarOf (c • μ) = c • multHaarOf μ := by
  rw [multHaarOf, multHaarOf, unitsMeasureOf_smul, smul_comm]

theorem multHaarOf_eq (μ : Measure K) [μ.IsAddHaarMeasure] :
    multHaarOf μ = μ (𝒪[K] : Set K) • multHaar K := by
  conv_lhs => rw [eq_smul_haarIntegers μ]
  rw [multHaarOf_smul, multHaarOf_haarIntegers]

theorem unitsMeasureOf_eq (μ : Measure K) [μ.IsAddHaarMeasure] :
    unitsMeasureOf μ = ((1 - ((residueCard K : ℝ≥0∞))⁻¹) * μ (𝒪[K] : Set K)) • multHaar K := by
  have h : unitsMeasureOf μ = (multHaarConst K)⁻¹ • multHaarOf μ := by
    rw [multHaarOf, smul_smul, ENNReal.inv_mul_cancel multHaarConst_ne_zero multHaarConst_ne_top,
      one_smul]
  rw [h, multHaarOf_eq, smul_smul, multHaarConst, inv_inv]

instance (μ : Measure K) [μ.IsAddHaarMeasure] : (multHaarOf μ).IsHaarMeasure := by
  rw [multHaarOf_eq μ]
  have h0 : μ (𝒪[K] : Set K) ≠ 0 := by
    rw [← coe_valBall_zero]
    exact (isOpen_valBall 0).measure_ne_zero μ ⟨0, zero_mem _⟩
  have ht : μ (𝒪[K] : Set K) ≠ ∞ := by
    rw [← coe_valBall_zero]
    exact (isCompact_valBall 0).measure_lt_top.ne
  exact IsHaarMeasure.smul _ h0 ht

theorem multHaarOf_unitFiltrationUnits_zero (μ : Measure K) [μ.IsAddHaarMeasure] :
    multHaarOf μ (unitFiltrationUnits K 0 : Set Kˣ) = μ (𝒪[K] : Set K) := by
  rw [multHaarOf_eq, Measure.smul_apply, multHaar_unitFiltrationUnits_zero, smul_eq_mul, mul_one]

theorem multHaarOf_selfDualMeasure (ψ : AddChar K Circle) :
    multHaarOf (selfDualMeasure ψ) =
      (((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ≥0) : ℝ≥0∞) • multHaar K := by
  rw [multHaarOf_eq, selfDualMeasure_integers]

theorem unitsMeasureOf_selfDualMeasure (ψ : AddChar K Circle) :
    unitsMeasureOf (selfDualMeasure ψ) =
      ((1 - ((residueCard K : ℝ≥0∞))⁻¹) *
        (((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ≥0) : ℝ≥0∞)) • multHaar K := by
  rw [unitsMeasureOf_eq, selfDualMeasure_integers]

namespace Padic

variable (p : ℕ) [Fact p.Prime] (K) [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

theorem multHaarOf_selfDualMeasure_stdCharOf_units :
    multHaarOf (selfDualMeasure (stdCharOf p K)) (unitFiltrationUnits K 0 : Set Kˣ) =
      ((Nat.card (𝒪[K] ⧸ differentIdeal 𝒪[ℚ_[p]] 𝒪[K]) : ℝ≥0) ^ (-(1 / 2 : ℝ)) : ℝ≥0) := by
  rw [multHaarOf_unitFiltrationUnits_zero, selfDualMeasure_stdCharOf_integers]

end Padic

end GroundTheory.LocalField
