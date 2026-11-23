import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers

noncomputable section

namespace GlobalTheory.LiftLeaf

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem atMOfParam_rec {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) : AtMOfParam N A i := by
  intro x _ Sig hX σ hW
  obtain ⟨P, hP, hB⟩ := hX
  refine ⟨Sig, hW, x, fun w hw => ⟨heckePol N i x w, ?_, rfl⟩⟩
  rw [hB.2.2.2.1 w hw.1]
  exact A.pt_loc i P x hP w hw

theorem atMOfParam (D : D7) (i : D.nd.Loc) : AtMOfParam D.nd D.naut i :=
  atMOfParam_rec D.nd D.naut i

end GlobalTheory.LiftLeaf
