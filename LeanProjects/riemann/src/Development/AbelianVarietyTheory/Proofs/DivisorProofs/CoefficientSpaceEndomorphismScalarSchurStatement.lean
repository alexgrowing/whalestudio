import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpaceEndomorphismScalarSchur
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientSpace_endomorphism_scalar_schur : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g : Module.End K (VV K lam)),
    (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∃ a : K, ∀ v, g v = a • v := by
  first | exact @GlobalTheory.CoefSchur.endo_scalar | exact GlobalTheory.CoefSchur.endo_scalar | (intros; apply GlobalTheory.CoefSchur.endo_scalar <;> assumption)
