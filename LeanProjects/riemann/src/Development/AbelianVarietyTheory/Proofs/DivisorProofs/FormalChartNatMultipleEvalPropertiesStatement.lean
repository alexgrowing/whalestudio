import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartNatMultipleEvalProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_natMultiple_eval_properties : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n k, (∀ i, c.ev n (nmul c.μ k i) = mulBy O (G.A n) k (c.x n i)) ∧ (∀ f, c.ev n (subst (nmul c.μ k) f) = mulBy O (G.A n) k (c.ev n f)) ∧ ∀ s, c.ev₂ n (pull2 (nmul c.μ k) s) = pullbackTwo (mulBy O (G.A n) k) (c.ev₂ n s) := by
  first | exact @GlobalTheory.QLog.ChartMul.nmul_ev | exact GlobalTheory.QLog.ChartMul.nmul_ev | (intros; apply GlobalTheory.QLog.ChartMul.nmul_ev <;> assumption)
