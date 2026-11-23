import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacC
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualType_residueChars_unramified_tuple : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ν : Twist D Circle), ν.Good → B.admitted ν.Q → (∀ PP ∈ allP B ν.Q, GlobalTheory.StepLaw.ResAt (B.mu * ν.chi) PP (resP B ν PP) ∧ GlobalTheory.StepLaw.ResAt (B.mu * ν.chi * B.eta⁻¹) PP (resP B ν PP)) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi) (allP B ν.Q) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi * B.eta⁻¹) (allP B ν.Q) := by
  first | exact @GlobalTheory.ExportSeries.TupleChars.tuple_chars | exact GlobalTheory.ExportSeries.TupleChars.tuple_chars | (intros; apply GlobalTheory.ExportSeries.TupleChars.tuple_chars <;> assumption)
