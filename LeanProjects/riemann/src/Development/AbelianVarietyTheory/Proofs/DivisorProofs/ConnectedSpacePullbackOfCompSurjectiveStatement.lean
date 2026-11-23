import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpacePullbackOfCompSurjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedSpace_pullback_of_comp_of_surjective : ∀ (X P Q Z : Scheme.{0}) (a : X ⟶ P) (b : P ⟶ Q) (g : X ⟶ Q) (ν : Z ⟶ Q), a ≫ b = g → Surjective a → ConnectedSpace (pullback g ν : Scheme.{0}) → ConnectedSpace (pullback b ν : Scheme.{0}) := by
  first | exact @GlobalTheory.connectedSpace_pullback_of_comp_surjective | exact GlobalTheory.connectedSpace_pullback_of_comp_surjective | (intros; apply GlobalTheory.connectedSpace_pullback_of_comp_surjective <;> assumption)
