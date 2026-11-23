import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtSameMumfordBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TraitUnif

theorem exists_generic_fibre_pull : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W), Function.Injective φ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (AW : PolAV (Sp (FractionRing W))) (genW : ((Over.pullback (jK W)).obj ((Over.pullback (spMap φ)).obj G)) ≅ AW.A) (κ₁ : pullback ((Over.pullback (spMap φ)).obj G).hom (jK W) ⟶ pullback G.hom (jK R)), IsMonHom genW.hom ∧ κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst ((Over.pullback (spMap φ)).obj G).hom (jK W) ≫ pullback.fst G.hom (spMap φ) ∧ LBIso (AW.L.pull genW.hom.left) ((A.L.pull gen.hom.left).pull κ₁) := by
  intro R W _ _ _ _ _ _ φ hφ G _ _ A gen hgen
  haveI : IsMonHom gen.hom := hgen
  set gφ := IsFractionRing.map (K := FractionRing R) (L := FractionRing W) hφ with hgφ
  have hsq : jK W ≫ spMap φ = spMap gφ ≫ jK R := by
    simp only [hgφ, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have hmono : Mono (jK R) := by
    have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    infer_instance
  let GV := (Over.pullback (spMap φ)).obj G
  have hβ := isGrpPullback_pullback G (spMap φ)
  let κ₁ : pullback GV.hom (jK W) ⟶ pullback G.hom (jK R) :=
    pullback.lift (pullback.fst GV.hom (jK W) ≫ pullback.fst G.hom (spMap φ)) (pullback.snd GV.hom (jK W) ≫ spMap gφ)
      (by rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc])
  have hκf : κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst GV.hom (jK W) ≫ pullback.fst G.hom (spMap φ) :=
    pullback.lift_fst _ _ _
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK W)).obj GV).hom ≫ spMap gφ :=
    pullback.lift_snd _ _ _
  have hκ : IsGrpPullback ((Over.pullback (jK W)).obj GV) ((Over.pullback (jK R)).obj G) (spMap gφ) κ₁ :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback GV (jK W)).comp hβ).congr hsq hκf.symm) w
  have hκA : IsGrpPullback ((Over.pullback (jK W)).obj GV) A.A (spMap gφ) (κ₁ ≫ gen.hom.left) :=
    (hκ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  obtain ⟨P', g, hg, -, hmul, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap gφ) A
  have hP' : IsGrpPullback P'.A A.A (spMap gφ) g := by
    refine ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩
    have ex : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    have ey : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hmul]
    rfl
  obtain ⟨e, he, heq⟩ := grpPullback_iso hκA hP'
  refine ⟨P', e, κ₁, he, hκf, ?_⟩
  have h1 : LBIso (P'.L.pull e.hom.left) ((A.L.pull g).pull e.hom.left) :=
    GlobalTheory.FamRep.lbIso_pull (LBIso.symm ⟨t, ht⟩) _
  have h2 : LBIso ((A.L.pull g).pull e.hom.left) (A.L.pull (e.hom.left ≫ g)) :=
    GlobalTheory.FamRep.lbIso_pull_pull A.isLB g e.hom.left
  have h3 : LBIso ((A.L.pull gen.hom.left).pull κ₁) (A.L.pull (κ₁ ≫ gen.hom.left)) :=
    GlobalTheory.FamRep.lbIso_pull_pull A.isLB gen.hom.left κ₁
  rw [heq] at h2
  exact LBIso.trans (pull_isLB P'.isLB _) (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB (pull_isLB A.isLB _) _) h1
    (LBIso.trans (pull_isLB (pull_isLB A.isLB _) _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _) h2 h3.symm)

theorem extLam_pull_square : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)), IsGrpPullback G₁ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → κ₁ ≫ pullback.fst G.hom (jK R) = pullback.fst G₁.hom (jK R') ≫ β → ∀ (L : LB ((Over.pullback (jK R)).obj G).left) (N : LB ((Over.pullback (jK R')).obj G₁).left) (PP : LB (G2 G).left), L.IsLB → N.IsLB → LBIso N (L.pull κ₁) → ExtLam G L PP → ExtLam G₁ N (PP.pull β₂) := by
  intro R R' _ _ _ _ _ _ ρ hρ G _ _ G₁ _ _ β β₂ κ₁ hβ hsqβ hκf L N PP hL hN hNL hExt
  have hsq : jK R' ≫ spMap ρ =
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have hmono : Mono (jK R) := by
    have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    infer_instance
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK R')).obj G₁).hom ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) := by
    apply (cancel_mono (jK R)).1
    rw [Category.assoc, Category.assoc]
    change κ₁ ≫ pullback.snd G.hom (jK R) ≫ jK R = pullback.snd G₁.hom (jK R') ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R
    rw [← pullback.condition, ← Category.assoc, hκf, Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition,
      Category.assoc, hsq]
  have hκ : IsGrpPullback ((Over.pullback (jK R')).obj G₁) ((Over.pullback (jK R)).obj G)
      (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) κ₁ :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback G₁ (jK R')).comp hβ).congr hsq hκf.symm) w
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R')).obj G₁) := Functor.isCommMonObj_obj
  obtain ⟨β₂κ, hsqκ, Hκ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G₁) κ₁ hκ
  obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _ (isGrpPullback_pullback G (jK R))
  refine ⟨pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩
  have H1 := Hκ L N _ PP g₂ hL hN hExt.1 hNL (hExt.2 g₂ hg₂)
  have e : β₂κ ≫ g₂ = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (β₂κ ≫ g₂) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      rw [Category.assoc, hg₂.1, ← Category.assoc, hsqκ.1, Category.assoc, hκf, Category.assoc, hsqβ.1,
        reassoc_of% hκ₂.1]
    · show (β₂κ ≫ g₂) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      rw [Category.assoc, hg₂.2, ← Category.assoc, hsqκ.2, Category.assoc, hκf, Category.assoc, hsqβ.2,
        reassoc_of% hκ₂.2]
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hExt.1 _) (pull_isLB (pull_isLB hExt.1 _) _) H1
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => e) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

theorem exists_trait_unif_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G (spMap φ) βW ∧ Geo.Tor.IsSquare βW βW₂ ∧ LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  have := hR.1.1
  have := hR.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨AV, genV, κ₁, hgenV, hκ, hLV⟩ := exists_generic_fibre_pull R V φ hφ G A gen hgen
  obtain ⟨βV₂, hsqV, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G _ _ (isGrpPullback_pullback G (spMap φ))
  have hExtV := extLam_pull_square R V φ hφ G _ _ βV₂ κ₁ (isGrpPullback_pullback G (spMap φ)) hsqV hκ _ _ PP
    (pull_isLB A.isLB _) (pull_isLB AV.isLB _) hLV hPP
  have hGV : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback (spMap φ) G hG
  obtain ⟨R', _, _, _, ρ, D₁, G₁, _, _, β, β₂, A₁, U₁, hR', hρ, hβ, hsq, hLam⟩ :=
    GlobalTheory.T.exists_uniformisation_finiteExt_sameMumfordBundle V hV _ hGV AV genV hgenV _ hExtV
  have hρloc : IsLocalHom ρ := RingHom.IsIntegral.isLocalHom hρ.2.2.to_isIntegral hρ.2.1
  refine ⟨R', _, _, _, ρ.comp φ, G₁, _, _, β ≫ pullback.fst G.hom (spMap φ), β₂ ≫ βV₂, D₁, A₁, U₁, hR',
    hρ.2.1.comp hφ, ?_, ?_, ?_, ?_⟩
  · exact RingHom.isLocalHom_comp ρ φ
  · refine (hβ.comp (isGrpPullback_pullback G (spMap φ))).congr ?_ rfl
    simp [spMap, Spec.map_comp]
  · refine ⟨?_, ?_⟩
    · rw [Category.assoc, hsqV.1, ← Category.assoc, hsq.1, Category.assoc]
    · rw [Category.assoc, hsqV.2, ← Category.assoc, hsq.2, Category.assoc]
  · exact LBIso.trans (DVR.linComb_isLB _ U₁.LG.isLB _ _) (pull_isLB (pull_isLB hPP.1 _) _) (pull_isLB hPP.1 _) hLam
      (GlobalTheory.FamRep.lbIso_pull_pull hPP.1 βV₂ β₂)
end GlobalTheory.Mum.TraitUnif
