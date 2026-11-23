import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarried
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedSectionNonzeroNearClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameNearClosedFibrePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closed_spec {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (hS : IsSemiAbelian G)
    (y : G.left) (hy : G.hom y = closedPoint R) :
    ∃ y₀ : G.left, y ⤳ y₀ ∧ IsClosed ({y₀} : Set G.left) ∧ G.hom y₀ = closedPoint R := by
  have : QuasiCompact G.hom := hS.quasiCompact
  have hc : CompactSpace G.left := by
    constructor
    have := QuasiCompact.isCompact_preimage (f := G.hom) Set.univ isOpen_univ isCompact_univ
    simpa using this
  obtain ⟨y₀, hy₀, hcl⟩ := (isClosed_closure (s := ({y} : Set G.left))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  have hsp : y ⤳ y₀ := specializes_iff_mem_closure.2 hy₀
  refine ⟨y₀, hsp, hcl, ?_⟩
  have h1 : G.hom y ⤳ G.hom y₀ := hsp.map G.hom.continuous
  rw [hy] at h1
  have h2 := specializes_iff_mem_closure.1 h1
  exact (isClosed_singleton_closedPoint R).closure_subset h2

set_option maxHeartbeats 1000000 in

theorem FrameCarried.exists_near_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y = closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  obtain ⟨θ, hθ, O, hO, hnz⟩ := GlobalTheory.T.exists_carried_section_nonzero_near_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact
  obtain ⟨y₀, hsp, hcl, hy₀c⟩ := closed_spec G hS y hy
  obtain ⟨V, hV, rest⟩ := GlobalTheory.T.exists_frame_near_closedFibre_point R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact θ hθ O hO hnz y₀ hcl hy₀c
  exact ⟨V, hsp.mem_open V.isOpen hV, rest⟩

end GlobalTheory.Mum
