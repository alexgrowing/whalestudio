import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeries
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_harishChandra_discreteSeries : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T), ∃ M : UGKMod p q, M.M = D.HK := by
  first | exact @GlobalTheory.DiscreteSeriesUnitary.exists_unitary | exact GlobalTheory.DiscreteSeriesUnitary.exists_unitary | (intros; apply GlobalTheory.DiscreteSeriesUnitary.exists_unitary <;> assumption)
