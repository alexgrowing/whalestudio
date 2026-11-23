import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContChiRat

noncomputable section

namespace GlobalTheory.Pass.HfCharStep

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem main : StepHfChar := fun D _ HW F h hI i _ _ h2 w hw h1 =>
  GlobalTheory.HfCharProof.hfChar D HW F h hI i w hw h2 ((IntermediateField.finrank_eq_one_iff.mp h1).le.trans bot_le)

end GlobalTheory.Pass.HfCharStep

end
