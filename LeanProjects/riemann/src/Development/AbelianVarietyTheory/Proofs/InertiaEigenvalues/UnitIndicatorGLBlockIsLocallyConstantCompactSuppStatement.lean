import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockIsLocallyConstantCompactSupp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (r : ℕ), IsTest (unitG r F) := by
  first | exact @GlobalTheory.JR.UnitTest.unitG_isTest | exact GlobalTheory.JR.UnitTest.unitG_isTest | (intros; apply GlobalTheory.JR.UnitTest.unitG_isTest <;> assumption)
