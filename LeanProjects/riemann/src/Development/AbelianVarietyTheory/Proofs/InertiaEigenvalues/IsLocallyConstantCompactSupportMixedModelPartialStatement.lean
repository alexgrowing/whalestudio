import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportMixedModelPartial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → IsTest (WeilMix.ptrB M ψ f) := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_isTest | exact GlobalTheory.JR.WeilMix.ptrB_isTest | (intros; apply GlobalTheory.JR.WeilMix.ptrB_isTest <;> assumption)
