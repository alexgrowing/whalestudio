import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonLocalizationModel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_localization_model : ∀ {O F R R₂ : Type} [CommRing O] [Field F] [CommRing R] [CommRing R₂] (β : O →+* F) (r r₂ : O) (b : O →+* R)
    (b₂ : O →+* R₂) (ω : R →+* F) (ω₂ : R₂ →+* F), Models.IsDedFrac β → Models.IsDedFrac ω → Models.IsDedFrac ω₂ →
    ω.comp b = β → ω₂.comp b₂ = β → @IsLocalization.Away O _ r R _ b.toAlgebra →
    @IsLocalization.Away O _ r₂ R₂ _ b₂.toAlgebra → Algebra.FiniteType ℤ O →
    ∃ (ω' : Localization.Away (b r₂) →+* F) (h : R₂ →+* Localization.Away (b r₂)),
      ω'.comp (algebraMap R (Localization.Away (b r₂))) = ω ∧ ω'.comp h = ω₂ ∧ Models.IsDedFrac ω' ∧
      @Algebra.FiniteType ℤ (Localization.Away (b r₂)) _ CommRing.toCommSemiring.toSemiring (Ring.toIntAlgebra _) ∧ IsOpenImmersion (spMap b) ∧
      IsPullback (spMap (algebraMap R (Localization.Away (b r₂)))) (spMap h) (spMap b) (spMap b₂) ∧
      ∀ ω₂' : Localization.Away (b₂ r) →+* F, ω₂'.comp (algebraMap R₂ (Localization.Away (b₂ r))) = ω₂ →
        ∃ s : Localization.Away (b₂ r) →+* Localization.Away (b r₂), ω'.comp s = ω₂' := by
  first | exact @GlobalTheory.Member.overlap_rings | exact GlobalTheory.Member.overlap_rings | (intros; apply GlobalTheory.Member.overlap_rings <;> assumption)
