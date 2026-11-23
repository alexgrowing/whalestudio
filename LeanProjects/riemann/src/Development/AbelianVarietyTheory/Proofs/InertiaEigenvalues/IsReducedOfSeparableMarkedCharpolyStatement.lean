import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpoly
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_of_separable_markedCharpoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P <;> assumption)
