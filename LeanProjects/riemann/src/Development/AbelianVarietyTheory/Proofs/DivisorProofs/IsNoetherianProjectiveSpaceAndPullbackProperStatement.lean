import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianProjectiveSpaceAndPullbackProper
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNoetherian_projectiveSpace_and_pullback_proper : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → ∀ N : ℕ, IsNoetherian (PSpace R N) ∧ IsNoetherian (pullback (PSpace.str R N) π) := by
  first | exact @GlobalTheory.Mum.pspace_noeth_and_pullback | exact GlobalTheory.Mum.pspace_noeth_and_pullback | (intros; apply GlobalTheory.Mum.pspace_noeth_and_pullback <;> assumption)
