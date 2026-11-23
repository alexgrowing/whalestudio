import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unif_trait_baseChange : ∀ (R R₂ W W₂ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] (ρ : R →+* R₂) (φ : R →+* W) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂), Base R → GlobalTheory.LN.CDvr W → GlobalTheory.LN.CDvr W₂ → FinExt σ → IsLocalHom σ → φ₂.comp ρ = σ.comp φ → Function.Injective φ₂ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left), IsGrpPullback G₂ G (spMap ρ) β → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left), IsGrpPullback GW G (spMap φ) βW → ∀ (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), ∃ (GW' : Over (Sp W₂)) (_ : GrpObj GW') (_ : IsCommMonObj GW') (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' ∧ IsGrpPullback GW' GW (spMap σ) τ ∧ βW' ≫ β = τ ≫ βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' ∧ LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) := by
  intro R R₂ W W₂ _ _ _ _ _ _ _ _ _ _ _ _ ρ φ σ φ₂ _ hW hW₂ hσ hloc hc hφ₂ G _ _ hG G₂ _ _ β hβ GW _ _ βW hβW DW AW UW
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have := hW.1
  have hWa : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hGW : IsSemiAbelian GW := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hβW (isGrpPullback_pullback G (spMap φ))
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ G hG)
  obtain ⟨D₁, hX, A₁, U₁, hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hWa hσ.1 σ hσ.2.1 (map_maximalIdeal_le σ) hGW UW
  have hτ : IsGrpPullback ((Over.pullback (specOf σ)).obj GW) GW (spMap σ) (pullback.fst GW.hom (specOf σ)) :=
    isGrpPullback_pullback GW (specOf σ)
  have hb : spMap σ ≫ spMap φ = spMap φ₂ ≫ spMap ρ := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  have hn := (hτ.comp hβW).congr hb rfl
  have hw : (pullback.fst GW.hom (specOf σ) ≫ βW) ≫ G.hom =
      (((Over.pullback (specOf σ)).obj GW).hom ≫ spMap φ₂) ≫ spMap ρ := by
    rw [hn.1.w]; exact (Category.assoc _ _ _).symm
  have h₁ := hβ.1.lift_fst _ _ hw
  have h₂ := hβ.1.lift_snd _ _ hw
  have hβ' : IsGrpPullback ((Over.pullback (specOf σ)).obj GW) G₂ (spMap φ₂) (hβ.1.lift _ _ hw) :=
    hβ.cancel (hn.congr rfl h₁.symm) h₂
  have hsq : jK W₂ ≫ spMap φ₂ =
      spMap (IsFractionRing.map (K := FractionRing R₂) (L := FractionRing W₂) hφ₂) ≫ jK R₂ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have cond : (pullback.fst ((Over.pullback (specOf σ)).obj GW).hom (jK W₂) ≫ hβ.1.lift _ _ hw) ≫ G₂.hom =
      (pullback.snd ((Over.pullback (specOf σ)).obj GW).hom (jK W₂) ≫
        spMap (IsFractionRing.map (K := FractionRing R₂) (L := FractionRing W₂) hφ₂)) ≫ jK R₂ := by
    rw [Category.assoc, h₂, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc]
  refine ⟨(Over.pullback (specOf σ)).obj GW, inferInstance, inferInstance, hβ.1.lift _ _ hw,
    pullback.fst GW.hom (specOf σ), D₁, A₁, U₁, pullback.lift _ _ cond, hβ', hτ, h₁, pullback.lift_fst _ _ _, ?_⟩
  obtain ⟨wL, hwL, -⟩ := hP.lg
  exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull U₁.LG.L _ _ rfl)
    (chartPullSame UW.LG.L _ (fun _ => (Iso.refl ((Over.pullback (specOf σ)).obj GW)).hom.left ≫
      pullback.fst GW.hom (specOf σ)) _ _ fun _ => by
        exact congrArg (_ ≫ ·) (Category.id_comp _).symm) ⟨wL, hwL⟩

end GlobalTheory.Mum
