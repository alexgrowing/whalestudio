import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowerEmbedding
import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_power_embedding : ∀ (D : D7) (p : ℕ) [Fact p.Prime], UnramE D p → ∀ τ : Emb D p, phiPow D 1 τ = τ.comp (D.host.sigmaOf (frobG D p) : D.host.E →+* D.host.E) := by
  first | exact @GlobalTheory.FrobEmb.phiPow_one_eq | exact GlobalTheory.FrobEmb.phiPow_one_eq | (intros; apply GlobalTheory.FrobEmb.phiPow_one_eq <;> assumption)
