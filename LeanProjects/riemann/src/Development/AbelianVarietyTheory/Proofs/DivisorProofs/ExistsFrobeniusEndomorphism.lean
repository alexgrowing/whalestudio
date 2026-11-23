import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotFrobGUnitRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobOverPtOver

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FrobPow

theorem frobOver_left_apply {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) (x : X.left) :
    (GlobalTheory.SS.FrobModel.frobOver X).left x = x := rfl

theorem frobOver_appLE {k : Type} [Field k] [Fintype k] (X : Over (Sp k)) (U : X.left.Opens)
    (h : U ≤ (GlobalTheory.SS.FrobModel.frobOver X).left ⁻¹ᵁ U) (s : Γ(X.left, U)) :
    ((GlobalTheory.SS.FrobModel.frobOver X).left.appLE U U h).hom s = s ^ Fintype.card k :=
  GlobalTheory.AbLaw.rs_self (X := X.left) h (s ^ Fintype.card k)

theorem exists_isFrob_pow : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K), ∃ π : End A, IsFrob π ∧
    (∀ x : A.X.left, (Hom.hom (A := A) (B := A) π).left x = x) ∧
    ∀ (U : A.X.left.Opens) (h : U ≤ (Hom.hom (A := A) (B := A) π).left ⁻¹ᵁ U) (s : Γ(A.X.left, U)),
      ((Hom.hom (A := A) (B := A) π).left.appLE U U h).hom s = s ^ Fintype.card K := by
  intro K _ _ A
  letI : IsMonHom (GlobalTheory.SS.FrobModel.frobOver A.X) := (GlobalTheory.SS.FrobModel.frobG_frobOver A.X).1
  exact ⟨Hom.mk (GlobalTheory.SS.FrobModel.frobOver A.X), GlobalTheory.AV.FrobEx.isFrob_frobOver K A,
    fun x => frobOver_left_apply A.X x, fun U h s => frobOver_appLE A.X U h s⟩

end GlobalTheory.AV.FrobPow
