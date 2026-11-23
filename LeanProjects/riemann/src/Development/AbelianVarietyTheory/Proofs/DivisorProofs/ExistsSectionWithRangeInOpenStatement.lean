import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_residueFieldPoint_smooth_completeLocal : ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'], IsAdicComplete (maximalIdeal R') R' → ∀ (ρ : R →+* R') (U : Over (Sp R)), Smooth U.hom → ∀ (x₀ : Sp (ResidueField R') ⟶ U.left), x₀ ≫ U.hom = spMap ((residue R').comp ρ) → ∀ O : U.left.Opens, Set.range x₀ ⊆ O → ∃ a : Sp R' ⟶ U.left, a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  first | exact @GlobalTheory.HenselLift.exists_lift_mem_open | exact GlobalTheory.HenselLift.exists_lift_mem_open | (intros; apply GlobalTheory.HenselLift.exists_lift_mem_open <;> assumption)
