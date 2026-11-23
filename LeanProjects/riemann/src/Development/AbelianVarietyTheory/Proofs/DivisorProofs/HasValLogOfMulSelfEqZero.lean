import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.SqZero

theorem mvPolynomialEval_truncFinsupp_eq_sum_coeff_mul_prod {R σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ] (w : σ → R)
    (n : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    MvPolynomial.eval w (trunc' R n f) = ∑ β ∈ Finset.Iic n, coeff β f * ∏ i ∈ β.support, w i ^ β i := by
  have hsub : (trunc' R n f).support ⊆ Finset.Iic n := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, coeff_trunc'] at hm
    split_ifs at hm with h
    · exact Finset.mem_Iic.mpr h
    · exact absurd rfl hm
  rw [MvPolynomial.eval_eq, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [coeff_trunc', if_pos (Finset.mem_Iic.mp hm)]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

theorem hasVal_log_of_mul_self_eq_zero :
    ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (p : ℕ) (x : B), x * x = 0 → HasVal p (fun _ : Unit => x) (PowerSeries.log Q : MvPowerSeries Unit Q) (algebraMap B Q x) := by
  intro B Q _ _ _ _ p x hx
  set y : Q := algebraMap B Q x with hy
  have hyy : y * y = 0 := by rw [hy, ← map_mul, hx, map_zero]
  have hcoeff : ∀ β : Unit →₀ ℕ, coeff β (PowerSeries.log Q : MvPowerSeries Unit Q) =
      PowerSeries.coeff (β ()) (PowerSeries.log Q) := by
    intro β
    rw [PowerSeries.coeff_def (by rfl)]
  intro m
  refine ⟨1, fun N' hN' => ⟨0, ?_⟩⟩
  rw [mul_zero, map_zero, sub_eq_zero, mvPolynomialEval_truncFinsupp_eq_sum_coeff_mul_prod]
  rw [Finset.sum_eq_single (Finsupp.single () 1)]
  · rw [hcoeff]
    simp [PowerSeries.coeff_log, hy]
  · intro β _ hβ
    rw [hcoeff, PowerSeries.coeff_log]
    by_cases h0 : β () = 0
    · simp [h0]
    · have h1 : β () ≠ 1 := by
        intro h1; apply hβ; ext u; simp [h1]
      have hsupp : β.support = {()} := by
        ext u; simp [h0]
      rw [hsupp, Finset.prod_singleton]
      obtain ⟨k, hk⟩ : ∃ k, β () = k + 2 := ⟨β () - 2, by omega⟩
      have hp : (algebraMap B Q) ((fun _ : Unit => x) ()) ^ (k + 2) = 0 := by
        show y ^ (k + 2) = 0
        rw [pow_add, pow_two, hyy, mul_zero]
      rw [hk, hp, mul_zero]
  · intro h
    exfalso; apply h
    rw [Finset.mem_Iic]
    intro u
    simpa using hN'

end GlobalTheory.QLog.SqZero
