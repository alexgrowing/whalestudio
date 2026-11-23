import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendPointValuationRingOfDominatingLocalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFlatPointAtGenericPointsStatement
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

namespace GlobalTheory.ValuativeFlat

theorem isProper_of_lift_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s → Flat s → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* V) (x : Sp K ⟶ X), x ≫ s = spMap ((algebraMap V K).comp β) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (_ : Field L) (_ : Algebra V W) (_ : Algebra W L) (_ : Algebra K L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsLocalHom (algebraMap V W) ∧ ∃ f : Sp W ⟶ X, spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f) → IsProper s := by
  intro R _ _ _ _ X s hq hflat h
  have hq' : IsQProjOver (s ≫ 𝟙 (Sp R)) := by rwa [Category.comp_id]
  have hP := GlobalTheory.ValuativeGeneric.isProper_of_lift_generic R X (Sp R) s (𝟙 _) inferInstance hq' ?_
  · exact hP
  intro V K _ _ _ _ _ _ _ x y hx hxy
  let β : R →+* V := (Spec.preimage y).hom
  have hy : y = spMap β := by simp [β, spMap]
  have hxs : x ≫ s = spMap ((algebraMap V K).comp β) := by
    rw [hxy, hy, spMap, spMap, ← Spec.map_comp]; rfl
  have hinj : Function.Injective ((algebraMap V K).comp β) :=
    GlobalTheory.T.injective_of_flat_point_at_generic_points R K X s x _ hflat hx hxs
  have : CharZero K := charZero_of_injective_ringHom hinj
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hc, hloc, f, hf⟩ := h V K β x hxs
  exact GlobalTheory.T.descend_point_valuationRing_of_dominating_local_domain V K W L hc hloc X x f hf

end GlobalTheory.ValuativeFlat
