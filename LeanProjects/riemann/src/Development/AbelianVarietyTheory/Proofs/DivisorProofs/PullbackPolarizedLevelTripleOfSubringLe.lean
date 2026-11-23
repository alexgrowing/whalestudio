import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegBaseChange

open GlobalTheory.CechPic

theorem spMap_subtype_comp_inclusion {R : Type} [CommRing R] {R₁ R₂ : Subring R} (h : R₁ ≤ R₂) :
    spMap R₂.subtype ≫ spMap (Subring.inclusion h) = spMap R₁.subtype := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem pullbackTriple_of_le : ∀ (R : Type) [CommRing R] (R₁ R₂ : Subring R) (h : R₁ ≤ R₂) (g M : ℕ) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std g M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), IsAbelianScheme A₁ → SmoothOfRelativeDimension g A₁.hom → P.IsLB → P₁.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → ∃ (A₂ : Over (Sp R₂)) (_ : GrpObj A₂) (lv₂ : Std g M → (𝟙_ (Over (Sp R₂)) ⟶ A₂)) (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₂ ∧ SmoothOfRelativeDimension g A₂.hom ∧ IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π ∧ Geo.Tor.IsSquare π π₂ ∧ IsPullbackTriple A P lv A₂ (P₁.pull π₂) lv₂ (spMap R₂.subtype) := by
  intro R _ R₁ R₂ h g M A _ P lv A₁ _ P₁ lv₁ hab hsm hP hP₁ H
  haveI := hab.comm
  obtain ⟨φ, φ₂, hφ, s₁, s₂, iso, hl⟩ := H
  have e := spMap_subtype_comp_inclusion h
  have pb₂ := Pdiv.PullbackComparison.isGrpPullback (spMap (Subring.inclusion h)) A₁
  have sq₂ := Pdiv.PullbackComparison.isSquare (spMap (Subring.inclusion h)) A₁
  have hw : φ ≫ A₁.hom = (A.hom ≫ spMap R₂.subtype) ≫ spMap (Subring.inclusion h) := by
    rw [hφ.1.w, Category.assoc, e]
  let ψ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₁).left := pb₂.1.lift φ _ hw
  have hψ₁ : ψ ≫ Pdiv.PullbackComparison.pφ (spMap (Subring.inclusion h)) A₁ = φ := pb₂.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ ((Over.pullback (spMap (Subring.inclusion h))).obj A₁).hom = A.hom ≫ spMap R₂.subtype :=
    pb₂.1.lift_snd _ _ _
  have hψ : IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₁) (spMap R₂.subtype) ψ :=
    pb₂.cancel (by rw [hψ₁, e]; exact hφ) hψ₂
  obtain ⟨ψ₂, sqψ⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ₂
  have hc : ψ₂ ≫ Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) A₁ = φ₂ :=
    GlobalTheory.SiegDesc.isSquare_comp hψ₁ sqψ sq₂ ⟨s₁, s₂⟩
  refine ⟨(Over.pullback (spMap (Subring.inclusion h))).obj A₁, inferInstance,
    fun a => GlobalTheory.SiegelPull.secPull pb₂ (lv₁ a), Pdiv.PullbackComparison.pφ _ A₁, Pdiv.PullbackComparison.pφ₂ _ A₁, ?_, ?_, pb₂, sq₂,
    ψ, ψ₂, hψ, sqψ.1, sqψ.2, ?_, fun a => ?_⟩
  · exact
      { comm := inferInstance
        smooth := by have := hab.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := hab.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := hab.geomConnected
          show GeometricallyConnected (pullback.snd _ _); infer_instance }
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback pb₂.1 hsm
  · have hP₂ := pull_isLB hP₁ (Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) A₁)
    refine (cls_eq_iff hP (pull_isLB hP₂ ψ₂)).1 ?_
    rw [(cls_eq_iff hP (pull_isLB hP₁ φ₂)).2 iso, cls_pull hP₂ ψ₂, cls_pull hP₁ _ hP₂, ← pull_comp, hc]
    rfl
  · apply pb₂.1.hom_ext
    · rw [Category.assoc, hψ₁, hl a, Category.assoc, GlobalTheory.SiegelPull.secPull_left, ← Category.assoc, e]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (lv a), Category.assoc, Over.w]
      rfl

end GlobalTheory.SiegBaseChange
