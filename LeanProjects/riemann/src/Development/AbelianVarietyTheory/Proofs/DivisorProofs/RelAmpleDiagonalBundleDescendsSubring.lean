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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleDiagSubring

theorem relAmple_diag_subring : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → Out.RelAmple A (diagPull A P) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → Out.RelAmple A₂ (diagPull A₂ (P₁.pull π₂)) := by
  intro R _ R₁ _ A _ P A₁ _ P₁ φ φ₂ hA₁ hP hP₁ hφ sq e hamp
  classical
  have := hA₁.proper
  have := hA₁.smooth
  let M : LB A₁.left := diagPull A₁ P₁
  have hM : M.IsLB := pull_isLB hP₁ _
  have hL : (diagPull A P).IsLB := pull_isLB hP _
  have e' : LBIso (diagPull A P) (M.pull φ) := GlobalTheory.SiegelPull.diag_iso sq e
  have hspan := GlobalTheory.CompanionTheory.PolSpread.span_good R₁.subtype A A₁ hM hL hφ.1 e' hamp
  have h1 : (1 : R) ∈ Ideal.span (R₁.subtype '' GlobalTheory.CompanionTheory.PolSpread.good A₁ M) := by rw [hspan]; trivial
  obtain ⟨c, hc, hs⟩ := Submodule.mem_span_set.1 h1
  choose! t ht hty using fun y (hy : y ∈ c.support) => hc hy
  refine ⟨c.support.image c, fun R₂ h hF A₂ _ π π₂ hπ sq₂ => ?_⟩
  let τ : R₁ →+* R₂ := Subring.inclusion h
  have hmem : ∀ y ∈ c.support, c y ∈ R₂ := fun y hy =>
    hF (Finset.mem_coe.2 (Finset.mem_image_of_mem c hy))
  have hT : Ideal.span (τ '' (t '' (c.support : Set R))) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : R₂) = ∑ y ∈ c.support.attach, (⟨c y.1, hmem y.1 y.2⟩ : R₂) * τ (t y.1) := by
      apply Subtype.ext
      refine (OneMemClass.coe_one R₂).trans (hs.symm.trans ?_)
      rw [Finsupp.sum, ← Finset.sum_attach]
      simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, smul_eq_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have : ((τ (t y.1) : R₂) : R) = y.1 := hty y.1 y.2
      rw [this]
    rw [e1]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨t y.1, ⟨y.1, y.2, rfl⟩, rfl⟩)
  have hB := GlobalTheory.CompanionTheory.PolSpread.relAmple_of_span τ A₁ hM _
    (by rintro _ ⟨y, hy, rfl⟩; exact ht y hy) hT
  have hπ' : Out.RelAmple (Over.mk A₂.hom) (M.pull π) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback A₁.hom (spMap τ)) hπ.1 (𝟙 _)
      (Category.id_comp _) (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) hB
  have : IsProper (Over.mk A₂.hom).hom := MorphismProperty.of_isPullback (P := @IsProper) hπ.1 ‹_›
  have hMπ : (M.pull π).IsLB := pull_isLB hM π
  have hL₂ : (diagPull A₂ (P₁.pull π₂)).IsLB := pull_isLB (pull_isLB hP₁ π₂) _
  have e₂ : LBIso (diagPull A₂ (P₁.pull π₂)) (M.pull π) :=
    GlobalTheory.SiegelPull.diag_iso sq₂ (GlobalTheory.lbIso_refl (pull_isLB hP₁ π₂))
  have e₃ : LBIso (M.pull π) ((M.pull π).pull (𝟙 _)) :=
    GlobalTheory.FibreAmple.lbIso_pull_comp (Category.id_comp π).symm (GlobalTheory.lbIso_refl hMπ)
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (A := Over.mk A₂.hom) (A' := A₂) (f := 𝟙 _) (φ := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) hMπ hL₂
    (LBIso.trans hL₂ hMπ (pull_isLB hMπ _) e₂ e₃) hπ'

end GlobalTheory.AmpleDiagSubring
