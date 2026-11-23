import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfLieReg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_of_lieReg' : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg <;> assumption)
