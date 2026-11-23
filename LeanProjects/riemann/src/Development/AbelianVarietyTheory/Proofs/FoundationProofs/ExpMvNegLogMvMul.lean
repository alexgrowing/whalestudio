import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogMv

open PowerSeries

theorem coeff_subst_range {K σ : Type*} [CommRing K] {G : MvPowerSeries σ K}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries K) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (f.subst G) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
        coeff n f * MvPowerSeries.coeff α (G ^ n) := by
  rw [coeff_subst (HasSubst.of_constantCoeff_zero hG),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1))]
  · rfl
  · intro k hk
    by_contra h
    apply hk
    have hlt : (α.sum fun _ k => k) < k := by simpa using h
    have h0 : MvPowerSeries.coeff α (G ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)
      exact_mod_cast hlt
    simp [h0]

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem expMv_eq_subst {G : MvPowerSeries σ ℂ_[p]} (hG : MvPowerSeries.constantCoeff G = 0) :
    expMv G = (exp ℂ_[p]).subst G := by
  ext α
  rw [coeff_subst_range hG]
  show expMv G α = _
  rw [expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_inv_mul]

theorem logMv_eq_subst {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 1) :
    GL3Theta.logMv F = (log ℂ_[p]).subst (F - 1) := by
  have h1 : MvPowerSeries.constantCoeff (F - 1) = 0 := by simp [hF]
  ext α
  rw [coeff_subst_range h1]
  show GL3Theta.logMv F α = _
  rw [GL3Theta.logMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_log]
  split_ifs
  · simp
  · simp
    ring

theorem exp_neg_log_one_var (K : Type*) [Field K] [CharZero K] :
    (exp K).subst (-log K) * (1 + X : PowerSeries K) = 1 := by
  have h0 : constantCoeff (-log K) = 0 := by simp
  have hs := HasSubst.of_constantCoeff_zero' h0
  have e : (1 + X) * d⁄dX K (log K) = 1 := by
    rw [deriv_log]
    ext n
    cases n with
    | zero => simp [add_mul]
    | succ n => simp [add_mul, coeff_succ_X_mul, coeff_one, pow_succ]
  refine derivative.ext ?_ ?_
  · rw [Derivation.leibniz, derivative_subst hs, derivative_exp, map_neg, derivative_one, map_add,
      derivative_one, derivative_X]
    simp only [smul_eq_mul]
    linear_combination (-(exp K).subst (-log K)) * e
  · have : constantCoeff ((exp K).subst (-log K) : PowerSeries K) = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
      · simp
      · intro k hk
        simp [hk]
    simp [this]

theorem expMv_neg_logMv_mul : ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (F : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff F = 1 → MvPowerSeries.constantCoeff (GL3Theta.logMv F) = 0 ∧ expMv (-GL3Theta.logMv F) * F = 1 := by
  intro p _ σ F hF
  have h1 : MvPowerSeries.constantCoeff (F - 1) = 0 := by simp [hF]
  have hs := HasSubst.of_constantCoeff_zero h1
  have h0 : MvPowerSeries.constantCoeff (GL3Theta.logMv F) = 0 := by
    rw [logMv_eq_subst hF]
    exact constantCoeff_subst_eq_zero h1 _ constantCoeff_log
  refine ⟨h0, ?_⟩
  have hl : HasSubst (-log ℂ_[p]) := HasSubst.of_constantCoeff_zero' (by simp)
  have e := congrArg (substAlgHom (R := ℂ_[p]) hs) (exp_neg_log_one_var ℂ_[p])
  have en : subst (F - 1) (-log ℂ_[p]) = -GL3Theta.logMv F := by
    rw [logMv_eq_subst hF, ← coe_substAlgHom hs, map_neg]
  rw [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom, subst_comp_subst_apply hl hs,
    en, add_sub_cancel] at e
  rw [expMv_eq_subst (by rw [map_neg, h0, neg_zero])]
  exact e

end GlobalTheory.ExpLogMv
