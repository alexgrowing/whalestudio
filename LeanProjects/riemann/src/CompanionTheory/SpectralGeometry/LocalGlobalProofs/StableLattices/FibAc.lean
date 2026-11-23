import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.CompanionTheory.PointSurjectivity

def FibAc {R : Type} [CommRing R] {X : Scheme.{0}} (a : X ⟶ Spec (CommRingCat.of R)) (N : LB X) : Prop :=
  ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
    (cechLB a N D).Acyclic

end GlobalTheory.CompanionTheory.PointSurjectivity
