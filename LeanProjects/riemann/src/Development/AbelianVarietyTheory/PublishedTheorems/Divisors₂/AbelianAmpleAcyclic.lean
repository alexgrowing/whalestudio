import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Published

def AbelianAmpleAcyclic : Prop :=
  ∀ (k : Type) [CommRing k] (S : Scheme.{0}) [IsLocallyNoetherian S] [ConnectedSpace S] (p : S ⟶ Sp k) (A : Over S)
    [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → CxForm.IsRelAcyclic (A.hom ≫ p) A.hom L

end GlobalTheory.Published
