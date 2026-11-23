import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftUniqueValuationRingAlgClosed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_lift_unique_valuationRing_algClosed : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ (u : Sp U ⟶ S) (n : ℕ), IsUnit (n : U) → ∀ y : Over.mk (spMap h ≫ u) ⟶ G, y ^ n = 1 → ∃! P : Over.mk u ⟶ G, P ^ n = 1 ∧ y.left = spMap h ≫ P.left := by
  first | exact @GlobalTheory.TorsionLiftVal.torsion_lift_unique | exact GlobalTheory.TorsionLiftVal.torsion_lift_unique | (intros; apply GlobalTheory.TorsionLiftVal.torsion_lift_unique <;> assumption)
