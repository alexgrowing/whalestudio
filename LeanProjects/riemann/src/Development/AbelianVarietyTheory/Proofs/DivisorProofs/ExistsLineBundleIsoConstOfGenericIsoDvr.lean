import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitRatioGenericLineBundleIsosStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenericIsoConst

theorem lbIso_of_generic : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left), P.IsLB → M.IsLB → LBIso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) → LBIso P M := by
  intro W K' _ _ _ _ _ _ G _ hG P M hP hM h
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  haveI : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ G.hom inferInstance inferInstance
  let ψ : K' ≃ₐ[W] FractionRing W := IsLocalization.algEquiv (nonZeroDivisors W) K' (FractionRing W)
  have e₂ : Out.jK W ≫ 𝟙 _ = spMap (ψ : K' →+* FractionRing W) ≫ spMap (algebraMap W K') := by
    have hr : (ψ : K' →+* FractionRing W).comp (algebraMap W K') = algebraMap W (FractionRing W) := by
      ext x; simp
    rw [Category.comp_id, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
  have h' : LBIso (P.pull (pullback.fst G.hom (Out.jK W))) (M.pull (pullback.fst G.hom (Out.jK W))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp
      (pullback.map G.hom (Out.jK W) G.hom (spMap (algebraMap W K')) (𝟙 _) (spMap (ψ : K' →+* FractionRing W)) (𝟙 _)
        (by simp) e₂) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm h
  exact GlobalTheory.lbIso_of_generic_normal_local W inferInstance inferInstance G.left G.hom (eSec G) inferInstance inferInstance
    inferInstance (Over.w η[G]) P M hP hM h'

open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh TopologicalSpace Opposite in

theorem globalFn_eq_cst : ∀ (W K' : Type) [CommRing W] [Field K'] [Algebra W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ f : Γ(pullback G.hom (spMap (algebraMap W K')), ⊤), ∃ c : K', f = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ c := by
  intro W K' _ _ _ G _ hG f
  have hU := GlobalTheory.AbCoh.uConst_of_isAbelianScheme W G hG K' (pullback G.hom (spMap (algebraMap W K')))
    (pullback.snd G.hom (spMap (algebraMap W K'))) (pullback.fst G.hom (spMap (algebraMap W K')))
    (IsPullback.of_hasPullback _ _)
  let g : C0 (OAff (pullback.snd G.hom (spMap (algebraMap W K')))) := fun T =>
    ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE le_top).op).hom f
  have hg : d0 _ g = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply]
    rw [Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, sub_eq_zero]
    exact Sec.res_res (pullback.snd G.hom (spMap (algebraMap W K'))) le_top (leOfHom φ.unop) f
  obtain ⟨r, hr, -⟩ := hU g hg
  refine ⟨r, TopCat.Presheaf.section_ext (pullback G.hom (spMap (algebraMap W K'))).sheaf ⊤ _ _ fun x hx => ?_⟩
  obtain ⟨U, hUa, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp (pullback G.hom (spMap (algebraMap W K'))).isBasis_affineOpens hx
  have e1 : ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom f =
      ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r) := by
    refine (hr (op ⟨U, hUa⟩)).trans ?_
    show _ = GlobalTheory.AbLaw.rs _ (le_top : U ≤ ⊤) (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r)
    rw [GlobalTheory.AbLaw.rs_cst]
    rfl
  have h1 := TopCat.Presheaf.germ_res_apply (pullback G.hom (spMap (algebraMap W K'))).presheaf (homOfLE (le_top : U ≤ ⊤)) x hxU f
  have h2 := TopCat.Presheaf.germ_res_apply (pullback G.hom (spMap (algebraMap W K'))).presheaf (homOfLE (le_top : U ≤ ⊤)) x hxU
    (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r)
  exact h1.symm.trans ((congrArg _ e1).trans h2)

theorem exists_iso_const_of_generic : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), w.IsGen → w₁.IsGen → ∃ (v : LB.Iso P M) (c : K'), v.IsGen ∧ ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) _ c * ((pullback.fst G.hom (spMap (algebraMap W K'))).appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  intro W K' _ _ _ _ _ _ G _ hG P M N hP hM hN w w₁ hw hw₁
  have hP' := pull_isLB hP (pullback.fst G.hom (spMap (algebraMap W K')))
  have hM' := pull_isLB hM (pullback.fst G.hom (spMap (algebraMap W K')))
  obtain ⟨v, hv⟩ := lbIso_of_generic W K' G hG P M hP hM (LBIso.trans hP' hN hM' ⟨w₁, hw₁⟩ (LBIso.symm ⟨w, hw⟩))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_global_unit_ratio_generic_lineBundle_isos _ _ _ P M N hP hM hN w w₁ v hw hw₁ hv
  obtain ⟨c, hc⟩ := globalFn_eq_cst W K' G hG u.val
  refine ⟨v, c, hv, fun n i m hle => ?_⟩
  rw [hu n i m hle, hc, GlobalTheory.AbLaw.rs_cst]

end GlobalTheory.GenericIsoConst
