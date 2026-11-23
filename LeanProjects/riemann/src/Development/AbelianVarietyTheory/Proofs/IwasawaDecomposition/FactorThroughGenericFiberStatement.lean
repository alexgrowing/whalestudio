import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FactorThroughGenericFiber
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_through_generic_fiber : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (T : Scheme.{0}) (g : T ⟶ Sp O), Set.range g ⊆ Set.range (spMap (algebraMap O K)) → ∃ f : T ⟶ Sp K, f ≫ spMap (algebraMap O K) = g := by
  first | exact @GlobalTheory.factor_through_fractionField_of_range | exact GlobalTheory.factor_through_fractionField_of_range | (intros; apply GlobalTheory.factor_through_fractionField_of_range <;> assumption)
