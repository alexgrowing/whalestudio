import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

def PhiPowStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen →
      ∃ c : F, c ≠ 0 ∧ ∀ ss : Fin (k + 1) → Fam D.toPre F k,
        (∀ i : Fin k, PhiRel D.toPre F k p w (ss i.castSucc) (ss i.succ)) →
        Fam.IsSmul D.toPre F c (ss 0) (ss (Fin.last k))

end ReciprocityTheory.ChartRestriction.G.H1
