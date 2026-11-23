import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_evalSquare_properties : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 ∧ c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f ∧ c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) ∧ c.ev₂ n (cob1 c.μ f) = cobOne O (G.A n) (c.ev n f) := by
  first | exact @GlobalTheory.QLog.Chart.ev₂_eval | exact GlobalTheory.QLog.Chart.ev₂_eval | (intros; apply GlobalTheory.QLog.Chart.ev₂_eval <;> assumption)
