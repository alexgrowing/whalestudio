import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpRangePositiveSignPlace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jump_range_positive_sign_place : StepJumpDirect := by
  first | exact @GlobalTheory.Pass.stepJumpDirect_holds | exact GlobalTheory.Pass.stepJumpDirect_holds | (intros; apply GlobalTheory.Pass.stepJumpDirect_holds <;> assumption)
