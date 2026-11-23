import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQCoverUnimodular
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPQCover_unimodular : ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant ∧ LocallyCompactSpace T.G ∧ SecondCountableTopology T.G ∧ T2Space T.G := by
  first | exact @GlobalTheory.coverUnitary_unimodular | exact GlobalTheory.coverUnitary_unimodular | (intros; apply GlobalTheory.coverUnitary_unimodular <;> assumption)
