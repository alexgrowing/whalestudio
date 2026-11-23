import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendPointValuationRingOfDominatingLocalDomain
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
theorem _root_.GlobalTheory.T.descend_point_valuationRing_of_dominating_local_domain : ∀ (V K W L : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [IsLocalRing W] [Field L] [Algebra W L] [IsFractionRing W L] [Algebra V W] [Algebra K L], (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) → IsLocalHom (algebraMap V W) → ∀ (X : Scheme.{0}) (x : Sp K ⟶ X) (f : Sp W ⟶ X), spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x := by
  first | exact @GlobalTheory.descend_point_to_valuationRing_of_dominating_local_domain | exact GlobalTheory.descend_point_to_valuationRing_of_dominating_local_domain | (intros; apply GlobalTheory.descend_point_to_valuationRing_of_dominating_local_domain <;> assumption)
