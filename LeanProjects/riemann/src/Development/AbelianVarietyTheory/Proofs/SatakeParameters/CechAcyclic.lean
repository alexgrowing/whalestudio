import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

abbrev toAb {R : Type} [CommRing R] (F : Shv R) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} :=
  F.obj ⋙ forget₂ (ModuleCat.{1} (ULift.{1} R)) AddCommGrpCat.{1}

def cechComplex (P : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) {U V : Scheme.{0}} (π : V ⟶ U) :
    CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj ((Arrow.mk π).cechNerve.rightOp ⋙ P)

def CechAcyclic (P : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) {U V : Scheme.{0}} (π : V ⟶ U) : Prop :=
  ∀ n : ℕ, (cechComplex P π).ExactAt (n + 1)

end GlobalTheory.Et

end
