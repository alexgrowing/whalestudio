import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingElementOfLocalFieldPointValues
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_element_of_local_field_point_values : ∀ (R : Type) [CommRing R] (P : (K : Type) → [Field K] → (R →+* K) → K → Prop), (∀ (K : Type) [Field K] (i : R →+* K) (u v : K), P K i u → P K i v → u = v) → (∀ p : Ideal R, p.IsPrime → ∃ f ∉ p, ∃ c : Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K), P K (j.comp (algebraMap R (Localization.Away f))) (j c)) → ∃ c : R, ∀ (K : Type) [Field K] (i : R →+* K), P K i (i c) := by
  first | exact @GlobalTheory.glue_field_points | exact GlobalTheory.glue_field_points | (intros; apply GlobalTheory.glue_field_points <;> assumption)
