import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOfGalAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNearGaloisQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapClosedPointOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_galois_action : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalAct ρ hD U' → Has D := by
  intro R R' _ _ _ _ _ _ ρ hB hF hG D D' hD A' G' _ _ hG' U' a
  obtain ⟨N, hL, hinv⟩ := exists_near_galois_quotient R hB R' ρ hF hG D D' hD A' G' hG' U' a
  have hP : IsProper (spMap ρ) := by
    have : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
    infer_instance
  have hS : Surjective (spMap ρ) := ⟨hF.2.2.to_isIntegral.comap_surjective hF.2.1⟩
  obtain ⟨G, _, _, β, i, hGs, hpb, -, hu⟩ :=
    descend_of_near R hB.1 (Sp R') (spMap ρ) hP hS inferInstance G' hG' N hL
  exact has_of_galAct R hB R' ρ hF hG D D' hD A' G' hG' U' a G β hGs hpb fun σ =>
    comp_eq_of_near ρ hF.2.2 G' hG' N G hGs.separated β hpb.1.w i hu σ (a.act σ) (a.cart σ).1.w (hinv σ)

end GlobalTheory.Mum
