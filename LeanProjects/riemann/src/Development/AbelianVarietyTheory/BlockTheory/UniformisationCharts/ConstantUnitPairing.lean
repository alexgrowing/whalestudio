import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

def constUnit (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (ζ : Fˣ) : Γ((TFK (R := R) F).left, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ

theorem ΓSpecIso_hom_constUnit (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (ζ : Fˣ) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      (constUnit R F ζ : Γ((TFK (R := R) F).left, ⊤)) = (ζ : F) :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply (ζ : F)

theorem constUnit_bijective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] : Function.Bijective (constUnit R F) :=
  (Units.mapEquiv
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

def MapCarriesPairing : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I →
    ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
      (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
      (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
      ∀ (p p' : QkPt D.toPre F k) (x x' : TFK (R := R) F ⟶ A.A),
        QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' →
        ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' (ζ : F) ↔
          WeilIs A.A A.L (k : ℤ) x x' (constUnit R F ζ)

end GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
