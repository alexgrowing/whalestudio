import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

def PhiFunStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen →
      ∃ Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k,
        ∀ s t : Fam D.toPre F k, PhiRel D.toPre F k p w s t ↔ t = Φ s

end ReciprocityTheory.ChartRestriction.G.DVR
