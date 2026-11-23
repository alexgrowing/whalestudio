import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitUniformisationPullbackFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOnTorusDescendsAlongLocalHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TqOfGtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLabelledCoverOfOddPrime
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EvenDesc

theorem isSemiAbelian_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β) (hG : IsSemiAbelian G) :
    IsSemiAbelian G' := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  haveI := he
  exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ G hG)

theorem mono_jK (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  haveI : Scheme.Spec.IsRightAdjoint := ΓSpec.adjunction.isRightAdjoint
  have : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))).op) := inferInstance
  exact this

end GlobalTheory.Mum.EvenDesc

set_option maxHeartbeats 2000000 in
open GlobalTheory.Mum.EvenDesc in

theorem GlobalTheory.Mum.evenOn_of_trait_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)) (P : GlobalTheory.UU.CP G₁), FinExt ρ → IsGrpPullback G₁ G (spMap ρ) β → κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β → LBIso (P.L.L.pull (pullback.fst G₁.hom (jK R'))) ((A.L.pull gen.hom.left).pull κ₁) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], Nonempty (GlobalTheory.UU.TQ (thickObj R' (maximalIdeal R') 0 G₁) X) → EvenOn P := by
  intro R _ _ _ hR G _ _ hG A gen hgen W _ _ _ φ GW _ _ βW DW AW UW κ hW hφi hφl hGW hκ hUW R' _ _ _ ρ G₁ _ _ β κ₁ P
    hfin hG₁ hκ₁ hP X _ _ _ hTQ

  have hgi : Function.Injective
      ((algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφi)
  obtain ⟨e, he⟩ := GlobalTheory.Mum.TraitExt.exists_fracHom ρ hfin.2.1 hfin.2.2 _ hgi
  obtain ⟨W₁, _, _, _, iw, φ₁, -, hW₁, hiwi, -, hiwl, hφ₁i, hφ₁l, hcomm, -, -⟩ :=
    GlobalTheory.T.exists_finite_complete_trait_extension_of_base R W R' hW φ hφi hφl ρ hfin (Kb W) e he
  have hAW : AdmBase W (maximalIdeal W) := by
    haveI := hW.1; exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hAW₁ : AdmBase W₁ (maximalIdeal W₁) := by
    haveI := hW₁.1; exact ⟨inferInstance, inferInstance, inferInstance, hW₁.2.1⟩
  have hGW' : IsSemiAbelian GW := isSemiAbelian_of_isGrpPullback hGW hG
  have hG₁' : IsSemiAbelian G₁ := isSemiAbelian_of_isGrpPullback hG₁ hG

  obtain ⟨hL5, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D'', hD'', A'', U'', hPu⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL5.polBaseChange h4.unifBaseChange
    h5.psiOnExists hAW hAW₁ iw hiwi (map_maximalIdeal_le iw) hGW' UW
  have hw1 : LBIso U''.LG.L
      (UW.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj GW)).hom.left ≫ pullback.fst GW.hom (specOf iw))) :=
    ⟨hPu.lg.choose, hPu.lg.choose_spec.1⟩

  have hpb1 : IsGrpPullback ((Over.pullback (specOf iw)).obj GW) GW (spMap iw) (pullback.fst GW.hom (specOf iw)) :=
    isGrpPullback_pullback GW (spMap iw)
  have hsp : spMap iw ≫ spMap φ = spMap φ₁ ≫ spMap ρ := by
    rw [GlobalTheory.Mum.TraitExt.spMap_comp, GlobalTheory.Mum.TraitExt.spMap_comp, hcomm]
  have hpb2 := hpb1.comp hGW
  have hsq : (pullback.fst GW.hom (specOf iw) ≫ βW) ≫ G.hom =
      ((Over.pullback (specOf iw)).obj GW).hom ≫ spMap φ₁ ≫ spMap ρ := by
    rw [← hsp, Category.assoc, hGW.1.w, ← Category.assoc, pullback.condition]
    rfl
  obtain ⟨β'', hβ1, hβ2⟩ : ∃ β'' : ((Over.pullback (specOf iw)).obj GW).left ⟶ G₁.left,
      β'' ≫ β = pullback.fst GW.hom (specOf iw) ≫ βW ∧
        β'' ≫ G₁.hom = ((Over.pullback (specOf iw)).obj GW).hom ≫ spMap φ₁ :=
    ⟨hG₁.1.lift _ _ hsq, hG₁.1.lift_fst _ _ _, hG₁.1.lift_snd _ _ _⟩
  have hpb3 : IsGrpPullback ((Over.pullback (specOf iw)).obj GW) G₁ (spMap φ₁) β'' :=
    hG₁.cancel (hpb2.congr hsp hβ1.symm) hβ2

  have hGW₁ : IsSemiAbelian ((Over.pullback (specOf iw)).obj GW) := IsSemiAbelian.pullback _ GW hGW'
  obtain ⟨P'', hP''L, hP''E⟩ := GlobalTheory.Mum.unif_evenOn W₁ hAW₁ D'' A'' _ hGW₁ U''

  have hprop : IsProper (pullback.snd ((Over.pullback (specOf iw)).obj GW).hom (jK W₁)) := by
    have hi : IsIso U''.gen.hom.left := ((Over.forget _).mapIso U''.gen).isIso_hom
    have := A''.isAb.proper
    have hw : pullback.snd ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) = U''.gen.hom.left ≫ A''.A.hom :=
      (Over.w U''.gen.hom).symm
    rw [hw]; infer_instance

  have c1 : pullback.fst GW.hom (specOf iw) ≫ GW.hom = ((Over.pullback (specOf iw)).obj GW).hom ≫ spMap iw :=
    pullback.condition
  have c2 : pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ ((Over.pullback (specOf iw)).obj GW).hom =
      pullback.snd ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ jK W₁ := pullback.condition
  have e1 : jK W₁ ≫ spMap iw = GlobalTheory.ArcPull.genMap hiwi ≫ jK W := by
    have := GlobalTheory.ArcPull.fracMap_sq hiwi
    rwa [Category.id_comp] at this
  have e2 : jK W₁ ≫ spMap φ₁ = GlobalTheory.ArcPull.genMap hφ₁i ≫ jK R' := by
    have := GlobalTheory.ArcPull.fracMap_sq hφ₁i
    rwa [Category.id_comp] at this
  obtain ⟨kW, hkW⟩ : ∃ kW : pullback ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ⟶ pullback GW.hom (jK W),
      kW ≫ pullback.fst GW.hom (jK W) =
        pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ pullback.fst GW.hom (specOf iw) := by
    refine ⟨pullback.lift _ (pullback.snd _ _ ≫ GlobalTheory.ArcPull.genMap hiwi) ?_, pullback.lift_fst _ _ _⟩
    rw [Category.assoc, c1, ← Category.assoc, c2, Category.assoc, Category.assoc, e1]
  obtain ⟨kG, hkG⟩ : ∃ kG : pullback ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ⟶ pullback G₁.hom (jK R'),
      kG ≫ pullback.fst G₁.hom (jK R') = pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ β'' := by
    refine ⟨pullback.lift _ (pullback.snd _ _ ≫ GlobalTheory.ArcPull.genMap hφ₁i) ?_, pullback.lift_fst _ _ _⟩
    rw [Category.assoc, hβ2, ← Category.assoc, c2, Category.assoc, Category.assoc, e2]
  have hkk : kW ≫ κ = kG ≫ κ₁ := by
    haveI := mono_jK R
    apply (cancel_mono (pullback.fst G.hom (jK R))).1
    rw [Category.assoc, Category.assoc, hκ, hκ₁, ← Category.assoc, ← Category.assoc, hkW, hkG, Category.assoc,
      Category.assoc, hβ1]
  have ga : LBIso (U''.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁)))
      (UW.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ pullback.fst GW.hom (specOf iw))) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso hw1 _ (by simp)
  have gb : LBIso (UW.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫
      pullback.fst GW.hom (specOf iw))) ((A.L.pull gen.hom.left).pull (kW ≫ κ)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp kW hkW.symm rfl hUW
  have gc : LBIso (P.L.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ β''))
      ((A.L.pull gen.hom.left).pull (kW ≫ κ)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp kG hkG.symm hkk hP
  have gd : LBIso (P.L.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ β''))
      ((P.L.L.pull β'').pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁))) :=
    GlobalTheory.GenSpread.lbIso_pull_pull P.L.isLB _ rfl
  have hLg : ((A.L.pull gen.hom.left).pull (kW ≫ κ)).IsLB := pull_isLB (pull_isLB A.isLB _) _
  have hgen' : LBIso (U''.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁)))
      ((P.L.L.pull β'').pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁))) :=
    LBIso.trans (pull_isLB U''.LG.isLB _) (pull_isLB UW.LG.isLB _) (pull_isLB (pull_isLB P.L.isLB _) _) ga
      (LBIso.trans (pull_isLB UW.LG.isLB _) hLg (pull_isLB (pull_isLB P.L.isLB _) _) gb
        (LBIso.trans hLg (pull_isLB P.L.isLB _) (pull_isLB (pull_isLB P.L.isLB _) _) gc.symm gd))

  haveI : IsNoetherianRing W₁ := hAW₁.1
  haveI : IsIntegrallyClosed W₁ := hAW₁.2.2.1
  haveI : Smooth ((Over.pullback (specOf iw)).obj GW).hom := hGW₁.smooth
  haveI : GeometricallyIntegral ((Over.pullback (specOf iw)).obj GW).hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hGW₁.smooth hGW₁.geomConnected
  have hLB : LBIso U''.LG.L (P.L.L.pull β'') :=
    GlobalTheory.Mum.lbIso_of_generic_local W₁ _ (eSec ((Over.pullback (specOf iw)).obj GW))
      (Over.w η[(Over.pullback (specOf iw)).obj GW]) _ _ U''.LG.isLB (pull_isLB P.L.isLB _) hgen'
  have hLB' : LBIso P''.L.L (P.L.L.pull β'') := by rw [hP''L]; exact hLB

  exact GlobalTheory.T.evenOnTorus_descends_along_localHom R' W₁ φ₁ hφ₁l G₁ hG₁' _ β'' hpb3 hprop P P'' hLB' hP''E X hTQ
