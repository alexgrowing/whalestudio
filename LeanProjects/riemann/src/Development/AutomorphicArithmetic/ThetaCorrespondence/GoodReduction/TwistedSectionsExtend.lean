import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.TwistIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionFieldRingEquivEqUnitMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearSymmFixesUnitSectionGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearModelFixesUnitSectionAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvrStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.IntegralSec

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.C1
open GlobalTheory GlobalTheory.SectionLattice

theorem twisted_sections_extend : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'] (D : Set (K' ≃ₐ[K] K')), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → (∀ σ ∈ D, ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K'))) → ∀ (H : LB A.left) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))), H.IsLB → M.IsLB → w.IsGen → ∀ σ ∈ D, ∀ (n : ℕ) (s : Fin n → H.Sec) (u : M.Sec) (c : Fin n → K'), GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull u (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) → ∃ u' : M.Sec, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull u' (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (σ (c k)) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) := by
  intro K W K' _ _ _ _ _ _ _ _ D hD hD' A _ hA G _ hG e he hφ H M w hH hM hw σ hσ n s u c hu
  obtain ⟨τ, φ, hτ, hφG, hφY⟩ := hφ σ hσ
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom
      (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp)
      (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫
      e.inv.left := ⟨_, rfl⟩
  rw [← hρ] at hφY
  have hA' : ρ ≫ (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) =
      e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) := by
    subst hρ
    have h := congrArg CommaMorphism.left e.inv_hom_id
    simp only [Over.comp_left, Over.id_left] at h
    simp only [Category.assoc]
    rw [reassoc_of% h]
    simp only [pullback.map, Category.id_comp, pullback.lift_fst, Category.comp_id]
  have hq : ρ ≫ pullback.snd G.hom (spMap (algebraMap W K')) =
      pullback.snd G.hom (spMap (algebraMap W K')) ≫ spMap (σ : K' →+* K') := by
    subst hρ
    have h₁ := Over.w e.inv
    have h₂ := Over.w e.hom
    simp only [Over.pullback_obj_hom] at h₁ h₂
    simp only [Category.assoc, h₁]
    simp only [pullback.map, pullback.lift_snd]
    rw [reassoc_of% h₂]
  obtain ⟨w₁, hw₁, hsec, hval⟩ := UpperTheory.Lit.Nos.twistIso M H (pullback.fst G.hom (spMap (algebraMap W K')))
    (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))
    (pullback.snd G.hom (spMap (algebraMap W K'))) ρ φ (σ : K' →+* K') hφY hA' hq hM hH w hw
  have he₀ : η[G].left ≫ G.hom = 𝟙 _ := by simpa using Over.w η[G]
  let x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')) :=
    pullback.lift (spMap (algebraMap W K') ≫ η[G].left) (𝟙 _)
      (by rw [Category.assoc, he₀]; simp)
  have hx₁ : x ≫ pullback.fst G.hom (spMap (algebraMap W K')) =
      spMap (algebraMap W K') ≫ η[G].left := pullback.lift_fst _ _ _
  have hx₂ : x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ := pullback.lift_snd _ _ _
  have hxρ : x ≫ ρ = spMap (σ : K' →+* K') ≫ x := by
    subst hρ
    exact GlobalTheory.T.semilinear_symm_fixes_unit_section_genericFibre K W K' A G e he σ x hx₁ hx₂
  have he₀φ := GlobalTheory.T.semilinearModel_fixes_unit_section_abelian W K' G hG (σ : K' →+* K') τ φ ρ hτ hφG hφY η[G].left he₀ x hx₁ hxρ
  have hv := GlobalTheory.T.dvr_fractionField_ringEquiv_eq_unit_mul W K' σ.toRingEquiv (hD σ hσ) (hD' σ hσ)
  have hHp : (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))).IsLB :=
    LB.isLB_pull hH _
  have hIAS := GlobalTheory.T.integral_twisted_comparison_at_fixed_section W K' G σ.toRingEquiv τ hv φ η[G].left he₀ he₀φ ρ x hx₁ hx₂ hxρ M _ hM hHp
    w w₁ (hval x hxρ)
  obtain ⟨v, c', hv', hrel⟩ := GlobalTheory.T.exists_lineBundleIso_const_of_genericIso_dvr W K' G hG (M.pull φ) M _ (LB.isLB_pull hM φ) hM hHp w w₁ hw hw₁
  exact UpperTheory.Lit.Nos.integralSec W K' G (M.pull φ) M _ (LB.isLB_pull hM φ) hM hHp w w₁ hw hw₁ hIAS v c' hv' hrel
    (GlobalTheory.Cartier.secPull u φ) _ (hsec n s u c hu)

end UpperTheory.Lit.Nos.C1
