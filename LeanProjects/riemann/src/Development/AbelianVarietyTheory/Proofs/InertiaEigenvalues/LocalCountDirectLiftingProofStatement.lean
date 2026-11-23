import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDirectLiftingProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCountDirectLifting_proof : StepLocDirect := by
  first | exact @GlobalTheory.Pass.LocDirect.main | exact GlobalTheory.Pass.LocDirect.main | (intros; apply GlobalTheory.Pass.LocDirect.main <;> assumption)
