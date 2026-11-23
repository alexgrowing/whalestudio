import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfLiftCompleteDvrCharZero
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
theorem _root_.GlobalTheory.T.isProper_of_lift_completeDvr_charZero : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s → Flat s → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* V) (x : Sp K ⟶ X), x ≫ s = spMap ((algebraMap V K).comp β) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (_ : Field L) (_ : Algebra V W) (_ : Algebra W L) (_ : Algebra K L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsLocalHom (algebraMap V W) ∧ ∃ f : Sp W ⟶ X, spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f) → IsProper s := by
  first | exact @GlobalTheory.ValuativeFlat.isProper_of_lift_dominating | exact GlobalTheory.ValuativeFlat.isProper_of_lift_dominating | (intros; apply GlobalTheory.ValuativeFlat.isProper_of_lift_dominating <;> assumption)
