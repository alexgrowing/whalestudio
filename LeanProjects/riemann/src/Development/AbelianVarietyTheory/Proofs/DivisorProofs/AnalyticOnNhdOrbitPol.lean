import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionPowAnalyticVectorNormLeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnalyticOnNhdOrbitOfDerivSeqNormEq
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg

open GlobalTheory.OrbitAnalytic in

theorem analyticOnNhd_orbit_pol : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Z ∈ upq (p * r + q * s) (p * s + q * r), ∀ (P : Pol p q r s), AnalyticOnNhd ℝ (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) Set.univ ∧ ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) 0 = F.ι ((omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) ^ k) P) := by
  intro p q r s T0 T1 T2 F Z hZ P
  set Y := Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z with hY
  let f : ℕ → ℝ → F.H := fun k t => F.Om (T0.expt (t • Z)) (F.ι ((omAct p q r s Y ^ k) P))
  have hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t := fun k t =>
    hasDerivAt_orbit (fun t => F.Om (T0.expt (t • Z)))
      (fun s t => by simp only [T0.expt_add Z hZ, map_mul]) _ _
      (by simpa only [pow_succ', Module.End.mul_apply] using F.der Z hZ ((omAct p q r s Y ^ k) P)) t
  have h0 : (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) = f 0 := by
    funext t; simp [f]
  rw [h0]
  refine ⟨fun a _ => ?_, fun k => ?_⟩
  · set S : ℝ := 4 * ∑ l, ∑ l', ‖Y l l'‖ with hS
    have hS0 : 0 ≤ S := by positivity
    refine analyticAt_of_bound f hf ((2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖) (S + 1)⁻¹
      (by positivity) (fun k t => ?_) a
    have hb := (GlobalTheory.T.fockAction_pow_analyticVector_norm_le p q r s F.H F.ι (isFockIsometry_of_fockData F) Y P.totalDegree k P le_rfl).2
    simp only [f]
    rw [F.isom]
    refine hb.trans ?_
    rw [← hS, inv_pow, div_inv_eq_mul]
    calc _ ≤ (S + 1) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((P.totalDegree : ℝ) / 2 + 1) * ‖F.ι P‖ := by
          gcongr; linarith
      _ = _ := by ring
  · have hit : ∀ k, iteratedDeriv k (f 0) = f k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [iteratedDeriv_succ, ih]; funext t; exact (hf k t).deriv
    rw [hit]
    simp [f, T0.expt_zero]

end GlobalTheory.FockAlg
