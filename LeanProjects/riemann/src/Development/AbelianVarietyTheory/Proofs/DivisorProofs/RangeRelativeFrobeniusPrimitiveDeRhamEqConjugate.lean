import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrpSchemeAbsoluteFrobeniusKillsHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

theorem span_pull_baseChange (H : GlobalTheory.Published.AbelianDeRham.BaseChange) {R R' : Type} [CommRing R]
    [CommRing R'] (σ : R →+* R') {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap σ) φ) {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) :
    Submodule.span R' (Set.range (GlobalTheory.PDiv.grpMor_of_isGrpPullback h).pull) = ⊤ ∧
      PrimitiveSubmodule A' = Submodule.span R' ((GlobalTheory.PDiv.grpMor_of_isGrpPullback h).pull '' PrimitiveSubmodule A) := by
  letI := σ.toAlgebra
  obtain ⟨hbc, hF⟩ := H R A g hA hg R' A' φ h
  refine ⟨Submodule.eq_top_iff'.2 fun x ↦ ?_, hF⟩
  obtain ⟨z, rfl⟩ := hbc.2 x
  induction z with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | tmul r c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ r (Submodule.subset_span ⟨c, rfl⟩)

theorem range_primPull_relFrob : GlobalTheory.Published.AbelianDeRham.BaseChange → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left) (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) (F : A ⟶ A₁) [IsMonHom F] (hF : F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A)) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LinearMap.range (primPull (dp0 R) (𝟙 _) F) = conjDR p R hR A ∧ PrimitiveSubmodule A₁ ≤ LinearMap.ker (primPull (dp0 R) (𝟙 _) F) := by
  intro H p _ R _ hR A A₁ _ _ π hπ F _ hF g hA hg
  obtain ⟨h1, h2⟩ := span_pull_baseChange H _ hπ hA hg
  have key : ∀ c, primPull (dp0 R) (𝟙 _) F ((GlobalTheory.PDiv.grpMor_of_isGrpPullback hπ).pull c) =
      frobDR p R hR A c := fun c ↦
    GrpMor.pull_pull (GlobalTheory.PDiv.grpMor_of_isGrpPullback hπ) (homMor (dp0 R) (𝟙 _) F)
      (frobMor p R hR A (cast_left p R hR A)) (fun _ ↦ rfl) hF c
  refine ⟨?_, ?_⟩
  · rw [LinearMap.range_eq_map, ← h1, Submodule.map_span, ← Set.range_comp, conjDR]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, key]
  · rw [h2, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, key]
    exact GlobalTheory.Published.ConjugateFiltration.Test.grpScheme_absoluteFrobenius_kills_hodgeFiltration p hR A (cast_left p R hR A)
      (frobMor p R hR A (cast_left p R hR A)) c hc

end GlobalTheory.ConjSeq
