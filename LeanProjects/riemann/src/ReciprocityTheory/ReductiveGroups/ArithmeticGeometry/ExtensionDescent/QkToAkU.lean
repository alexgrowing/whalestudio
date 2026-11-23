import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExpF

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def QkToAkU {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A) : Prop :=
  ∀ w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))), w.IsGen →
    QkToAk D.toPre F A k (U.ExpandsF F k w) p x

end ReciprocityTheory.ChartRestriction.G.Out
