import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepKerIsOpen
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualRep_ker_isOpen : ∀ (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → IsOpen ((redF D i ρ).ker : Set (G D.host.E D.nd.Om)) := by
  first | exact @GlobalTheory.TypeLeaf.redF_ker_isOpen | exact GlobalTheory.TypeLeaf.redF_ker_isOpen | (intros; apply GlobalTheory.TypeLeaf.redF_ker_isOpen <;> assumption)
