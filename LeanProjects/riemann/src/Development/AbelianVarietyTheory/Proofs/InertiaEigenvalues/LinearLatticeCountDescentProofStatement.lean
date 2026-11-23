import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearLatticeCountDescentProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearLatticeCountDescent_proof : LinearDescent := by
  first | exact @GlobalTheory.UnitLemma.Desc.linearDescent | exact GlobalTheory.UnitLemma.Desc.linearDescent | (intros; apply GlobalTheory.UnitLemma.Desc.linearDescent <;> assumption)
