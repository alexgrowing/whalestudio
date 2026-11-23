import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ggeo.DOpen

theorem isDerivAt0_lift_of_isOpenImmersion :
    ∀ (A T : Scheme.{0}) (φ : A ⟶ T) [IsOpenImmersion φ] (g : ℕ) (W : (Fin g → ℂ) → (Sp ℂ ⟶ A))
      (y : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ T),
      IsDerivAt0 (fun x => W x ≫ φ) y v → ∃ v' : Sp (DualNumber ℂ) ⟶ A, v' ≫ φ = v ∧ IsDerivAt0 W y v' := by
  intro A T φ _ g W y v hv
  have hcl : IsLocalRing.closedPoint (DualNumber ℂ) ∈ v ⁻¹ᵁ φ.opensRange := by
    have h0 : ⊤ ≤ (W 0 ≫ φ) ⁻¹ᵁ φ.opensRange := fun p _ =>
      (show (W 0 ≫ φ) p ∈ Set.range φ from ⟨W 0 p, by simp⟩)
    have hpt : v (IsLocalRing.closedPoint _) = (W 0 ≫ φ) ReciprocityTheory.ChartRestriction.G.PullbackSections.cpt := by
      have hcomp : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = W 0 ≫ φ := hv.1
      rw [← hcomp, Scheme.Hom.comp_apply, spMap, Spec_closedPoint]
    show v (IsLocalRing.closedPoint _) ∈ φ.opensRange
    rw [hpt]
    exact h0 trivial
  have htop : ⊤ ≤ v ⁻¹ᵁ φ.opensRange := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.dual_top_le _ hcl
  have hrange : Set.range v ⊆ Set.range φ := by
    rintro _ ⟨p, rfl⟩
    exact htop (show p ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
  obtain ⟨v', rfl⟩ : ∃ v', v' ≫ φ = v := ⟨IsOpenImmersion.lift φ v hrange, IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨v', rfl, ?_, fun U' h f' => ?_⟩
  · rw [← cancel_mono φ, Category.assoc]
    exact hv.1
  · have key : ∀ (U : T.Opens) (U' : A.Opens) (e : φ ⁻¹ᵁ U = U') (h : ⊤ ≤ v' ⁻¹ᵁ U') (f : Γ(T, U)),
        TrivSqZeroExt.snd (show DualNumber ℂ from
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
            ((v'.appLE U' ⊤ h).hom (φ.appLE U U' e.ge f))) =
          fderiv ℂ (fun z => valAt' (W z) U' (φ.appLE U U' e.ge f)) 0 y := by
      intro U U' e h f
      subst e
      have hU : ⊤ ≤ (v' ≫ φ) ⁻¹ᵁ U := h
      have happ : φ.appLE U (φ ⁻¹ᵁ U) (le_refl (φ ⁻¹ᵁ U)) f = φ.app U f := by
        rw [Scheme.Hom.app_eq_appLE]
      have hfun : (fun z => valAt' (W z) (φ ⁻¹ᵁ U) (φ.app U f)) =
          fun z => valAt' ((fun x => W x ≫ φ) z) U f :=
        funext fun z => ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_comp (W z) φ U f
      erw [happ]
      rw [hfun, ← hv.2 U hU f, Scheme.Hom.comp_appLE]
      rfl
    have hpre : φ ⁻¹ᵁ (φ ''ᵁ U') = U' := φ.preimage_image_eq U'
    have := key (φ ''ᵁ U') U' hpre h ((φ.appIso U').inv f')
    have hf : φ.appLE (φ ''ᵁ U') U' hpre.ge ((φ.appIso U').inv f') = f' := by
      have hh : φ.appLE (φ ''ᵁ U') U' hpre.ge = (φ.appIso U').hom := (Scheme.Hom.appIso_hom' φ U').symm
      rw [hh]
      exact ConcreteCategory.congr_hom (φ.appIso U').inv_hom_id f'
    rwa [hf] at this

end GlobalTheory.CompanionTheory.Ggeo.DOpen
