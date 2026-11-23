import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ExistsFgSmoothOfRelativeDimension
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeModelBaseChangeSubalgebra
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeSpreadsOutFiniteTypeSubringImports
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isCommMonObj_of_iso {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] {M N : C}
    [MonObj M] [MonObj N] [IsCommMonObj N] (e : M ≅ N) [IsMonHom e.hom] : IsCommMonObj M where
  mul_comm := by
    rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm N]

theorem isAbelianScheme_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G]
    [GrpObj (Over.mk (pullback.snd G.hom f))] (φ : pullback G.hom f ⟶ G.left)
    (h : IsGrpPullback (Over.mk (pullback.snd G.hom f)) G f φ) (hG : IsAbelianScheme G) :
    IsAbelianScheme (Over.mk (pullback.snd G.hom f)) := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  refine ⟨isCommMonObj_of_iso e, ?_, ?_, ?_⟩
  · show Smooth (pullback.snd G.hom f); infer_instance
  · show IsProper (pullback.snd G.hom f); infer_instance
  · show GeometricallyConnected (pullback.snd G.hom f); infer_instance

theorem exists_model_relDim : ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A] (F : Finset R),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B)
      (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧
        SmoothOfRelativeDimension g B.hom ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ g A _ F hA hg
  obtain ⟨S, B, instB, φ, hFS, hS, hB, hφ⟩ := GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring R A F hA
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have := hB.smooth
  have := hB.proper
  have hsnd : SmoothOfRelativeDimension g (pullback.snd B.hom (spMap (algebraMap S R))) := by
    have hp : IsPullback φ A.hom B.hom (spMap S.subtype) := hφ.1
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    have key : ∀ e : pullback B.hom (spMap S.subtype) ≅ A.left, e.hom ≫ A.hom = pullback.snd _ _ →
        SmoothOfRelativeDimension g (pullback.snd B.hom (spMap S.subtype)) := fun e he =>
      MorphismProperty.of_isPullback (IsPullback.of_horiz_isIso (fst := e.hom) (g := 𝟙 (Sp R))
        ⟨by rw [Category.comp_id, he]⟩) hg
    exact key hp.isoPullback.symm hp.isoPullback_inv_snd
  obtain ⟨R', hR'fg, hR'⟩ := exists_fg_smoothOfRelativeDimension S R B.left B.hom g inferInstance inferInstance hsnd
  obtain ⟨instB₂, φ₁, hB₂, hAB₂, -⟩ := model_passes_to_subalgebra S R A B φ hφ R'
  refine ⟨R'.toSubring, Over.mk (pullback.snd B.hom (spMap (algebraMap S R'))), instB₂, φ₁, ?_, ?_, ?_, hR', hAB₂⟩
  · intro x hx
    exact R'.algebraMap_mem ⟨x, hFS hx⟩
  · have : Algebra.FiniteType S R' := (Subalgebra.fg_iff_finiteType R').1 hR'fg
    have h1 : Algebra.FiniteType ℤ R' := Algebra.FiniteType.trans (S := S) hS this
    exact h1
  · exact isAbelianScheme_of_isGrpPullback _ hB₂ hB

end GlobalTheory.CompanionTheory.Ar.Approx
