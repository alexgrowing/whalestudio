import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.WcVol

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep (eq_one_or_eq_conj conj map_conj_eq continuous_conj modulus_algebraMap modulus_conj)

theorem measure_modulus_le (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ) (hR : 0 < R) :
    μ {w : E | (modulus w : ℝ) ≤ R} ≤
      ENNReal.ofReal ((μ (valBall E 0 : Set E)).toReal * R) := by
  have hq : (1 : ℝ) < (residueCard E : ℝ) := by exact_mod_cast one_lt_residueCard (K := E)
  have hq0 : (0 : ℝ) < (residueCard E : ℝ) := by linarith
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow hR hq
  have hsub : {w : E | (modulus w : ℝ) ≤ R} ⊆ (valBall E (-m) : Set E) := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0]; exact zero_mem _
    · refine SetLike.mem_coe.2 ((mem_valBall_iff_le_ord hw0).2 ?_)
      have h1 : (modulus w : ℝ) = (residueCard E : ℝ) ^ (-ord w) := by
        rw [modulus_of_ne_zero hw0]; push_cast; rfl
      have h2 : (residueCard E : ℝ) ^ (-ord w) < (residueCard E : ℝ) ^ (m + 1) := by
        rw [← h1]; exact lt_of_le_of_lt hw hm2
      have h3 := (zpow_lt_zpow_iff_right₀ hq).1 h2
      omega
  have hc : μ (valBall E 0 : Set E) ≠ ⊤ := (isCompact_valBall 0).measure_lt_top.ne
  refine (measure_mono hsub).trans ?_
  rw [measure_valBall μ (-m), neg_neg]
  have e1 : (((residueCard E : NNReal) ^ m : NNReal) : ENNReal) =
      ENNReal.ofReal ((residueCard E : ℝ) ^ m) := by
    rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
  rw [e1]
  conv_lhs => rw [← ENNReal.ofReal_toReal hc]
  rw [← ENNReal.ofReal_mul (zpow_nonneg hq0.le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hm1 ENNReal.toReal_nonneg

theorem volume_bound : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (σ : E ≃ₐ[F] E), σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure], ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : F, κ ≠ 0 → ∀ (ξ : E) (R : ℝ), 0 < R → μ {u : E | (modulus (algebraMap F E κ * σ u - ξ) : ℝ) ≤ R} ≤ ENNReal.ofReal (C * R / (modulus κ : ℝ) ^ 2) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ σ hσ μ _
  have hconj : σ = conj F E := (eq_one_or_eq_conj σ).resolve_left hσ
  subst hconj
  refine ⟨(μ (valBall E 0 : Set E)).toReal, ENNReal.toReal_nonneg, fun κ hκ ξ R hR => ?_⟩
  have ha : algebraMap F E κ ≠ 0 := (map_ne_zero _).2 hκ
  have hκ0 : modulus κ ≠ 0 := by
    rw [modulus_of_ne_zero hκ]; exact zpow_ne_zero _ residueCard_nnreal_ne_zero
  set a := algebraMap F E κ with ha_def
  set T : Set E := {w : E | (modulus w : ℝ) ≤ R} with hT_def
  have hT : MeasurableSet T :=
    measurableSet_le (measurable_coe_nnreal_real.comp measurable_modulus) measurable_const
  set Y : Set E := (fun v => v + -ξ) ⁻¹' T with hY_def
  have hY : MeasurableSet Y := hT.preimage (continuous_id.add continuous_const).measurable
  set Z : Set E := (fun v => a * v) ⁻¹' Y with hZ_def
  have hZ : MeasurableSet Z := hY.preimage (continuous_const.mul continuous_id).measurable
  have hS : {u : E | (modulus (a * conj F E u - ξ) : ℝ) ≤ R} = (conj F E) ⁻¹' Z := by
    ext u
    simp [hZ_def, hY_def, hT_def, sub_eq_add_neg]
  have e1 : μ ((conj F E) ⁻¹' Z) = μ Z := by
    have h := Measure.map_apply (μ := μ) (continuous_conj (K := F) (E := E)).measurable hZ
    rw [map_conj_eq] at h
    exact h.symm
  have e2 : μ Z = ((modulus a)⁻¹ : NNReal) * μ Y := by
    have h := Measure.map_apply (μ := μ) (measurable_const_mul a) hY
    rw [map_mul_left_eq_smul μ ha] at h
    exact h.symm
  have e3 : μ Y = μ T := measure_preimage_add_right μ (-ξ) T
  rw [hS, e1, e2, e3, modulus_algebraMap (K := F)]
  have hb := measure_modulus_le E μ R hR
  have hm : (0 : ℝ) < (modulus κ : ℝ) ^ 2 := by
    have : (0 : ℝ) < (modulus κ : ℝ) := by exact_mod_cast pos_iff_ne_zero.2 hκ0
    positivity
  have e4 : ((((modulus κ) ^ 2)⁻¹ : NNReal) : ENNReal) =
      ENNReal.ofReal (((modulus κ : ℝ) ^ 2)⁻¹) := by
    rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
  rw [e4]
  refine (mul_le_mul_right hb _).trans ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hm.le)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [div_eq_mul_inv, mul_comm]

end GlobalTheory.CompanionTheory.WcVol
