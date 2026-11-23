import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalLogCoeffMemOfSubOneMemDp
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ : Type) (h : MvPowerSeries σ B), constantCoeff h = 1 → (∀ α, coeff α (h - 1) ∈ J) → In J (formalLog (map (algebraMap B Q) h)) := by
  first | exact @GlobalTheory.DPLog.formalLog_in_of_sub_one_mem | exact GlobalTheory.DPLog.formalLog_in_of_sub_one_mem | (intros; apply GlobalTheory.DPLog.formalLog_in_of_sub_one_mem <;> assumption)
