import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_elements_from_idempotent_coeffs : StepCentral := by
  first | exact @GlobalTheory.Pass.CentralStep.main | exact GlobalTheory.Pass.CentralStep.main | (intros; apply GlobalTheory.Pass.CentralStep.main <;> assumption)
