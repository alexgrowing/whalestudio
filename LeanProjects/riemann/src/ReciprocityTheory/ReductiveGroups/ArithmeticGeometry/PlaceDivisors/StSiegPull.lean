import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace ReciprocityTheory.ChartRestriction.G.Pdiv

structure SiegPairPB {S S' : Scheme.{0}} {h M₁ : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}
    (o : SiegPre h M₁ ζ s) (f : S' ⟶ S) where
  A : Over S'
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  φ : A.left ⟶ o.A.left
  φ₂ : (G2 A).left ⟶ (G2 o.A).left
  pb : IsGrpPullback A o.A f φ
  sq : IsSquare φ φ₂
  P : LB (G2 A).left
  isLB : P.IsLB
  iso : LBIso P (o.P.pull φ₂)
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)

attribute [instance] SiegPairPB.grp SiegPairPB.comm

def StSiegPull : Prop :=
  ∀ {S S' : Scheme.{0}} {h M₁ : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}
    (o : SiegPre h M₁ ζ s) (f : S' ⟶ S), Nonempty (SiegPairPB o f)

end ReciprocityTheory.ChartRestriction.G.Pdiv
