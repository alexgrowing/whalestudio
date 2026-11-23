import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PuncturedPolydiscSumNegLogEqAndGeLogTwo
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (∑ i : Fin a, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp (Fin.castLE ha i)) = (∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) / (2 * Real.pi)) ∧ (0 < a → Real.log 2 ≤ ∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) := by
  first | exact @GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le | exact GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le | (intros; apply GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le <;> assumption)
