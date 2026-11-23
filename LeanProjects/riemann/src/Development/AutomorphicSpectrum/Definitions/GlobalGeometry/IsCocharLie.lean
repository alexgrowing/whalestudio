import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def charVal {A : Type} [CommRing A] {a : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X) (χ : X) : A :=
  (Spec.preimage (t.left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S) : Sp A ⟶ Spec (torusRing ZU X))).hom
    (AddMonoidAlgebra.single χ 1)

def KillsOver {G : Over S} [GrpObj G] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) {B : Type} [CommRing B]
    (b : Sp B ⟶ S) : Prop :=
  ∀ (A : Type) [CommRing A] (g : B →+* A) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X),
    (∀ y ∈ Y, charVal t y = 1) → t ≫ u = 1

def IsCocharLie {R : Type} [CommRing R] {x : Sp R ⟶ S} (M : LieModel (splitTorus S X) x (X →+ R)) : Prop :=
  ∀ (δ : X →+ R) (χ : X), charVal (M.pt δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ)

def LieModel.Lifts {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S}
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) (c : R →+* R') {S' : Scheme.{0}} {G' : Over S'}
    (φ : G'.left ⟶ G.left) {x' : Sp R' ⟶ S'} (e : E) (v : epsAt x' ⟶ G') : Prop :=
  v.left ≫ φ = spMap (dualMap c) ≫ (M.pt e).left

end GlobalTheory.CompanionTheory.Ar
