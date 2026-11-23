import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ExistsModelAbelianLb
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ExistsFgSmoothOfRelativeDimension
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeModelBaseChangeSubalgebra
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ImportsExtra
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ImportsFurther
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeSpreadsOut

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.KTrivSpread

open GlobalTheory.CompanionTheory.Ar.Approx

section Transport

variable {S S' : Scheme.{0}} {b : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
  {φ : G'.left ⟶ G.left}

theorem evc_lam {L : LB G.left} (hL : L.IsLB) (hP : (abelian₂ G L).IsLB) {Y : Over S} (a c : Y ⟶ G) :
    evc hP a c = lam (cls L hL) a c := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst G G) (snd G G) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem lam_eq (hφ : IsGrpPullback G' G b φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (e : LBIso L' (L.pull φ)) {X : Scheme.{0}} {s : X ⟶ S'} {s₀ : X ⟶ S} (hs : s ≫ b = s₀)
    (x y : Over.mk s ⟶ G') (x₀ y₀ : Over.mk s₀ ⟶ G) (hx : x.left ≫ φ = x₀.left) (hy : y.left ≫ φ = y₀.left) :
    lam (cls L' hL') x y = lam (cls L hL) x₀ y₀ := by
  have hc : cls L' hL' = CechPic.pull φ (cls L hL) := by
    rw [(cls_eq_iff hL' (pull_isLB hL φ)).2 e, cls_pull hL]
  simp only [lam, hc, ← pull_comp]
  rw [mul_left_comp hφ hs hx hy, hx, hy, one_left_comp hφ hs]

theorem triv_lam_iff (hφ : IsGrpPullback G' G b φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) (T : Over S') (y : T ⟶ G') :
    Triv (ev (abelian₂ G' L') (fst G' T) (snd G' T ≫ y)) ↔
      Triv (ev (abelian₂ G L) (fst G (Over.mk (T.hom ≫ b)))
        (snd G (Over.mk (T.hom ≫ b)) ≫ pushP hφ (s := T.hom) rfl y)) := by
  have hP : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hP' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  rw [triv_ev_iff hP', triv_ev_iff hP, evc_lam hL', evc_lam hL]
  have key : CechPic.pull (trR hφ T).left (lam (cls L' hL') (fst G' T) (snd G' T ≫ y)) =
      lam (cls L hL) (fst G (Over.mk (T.hom ≫ b)))
        (snd G (Over.mk (T.hom ≫ b)) ≫ pushP hφ (s := T.hom) rfl y) := by
    rw [pull_lam]
    have hs : ((snd G (Over.mk (T.hom ≫ b))).left ≫ T.hom) ≫ b = (G ⊗ Over.mk (T.hom ≫ b)).hom := by
      rw [Category.assoc]
      exact Over.w (snd G (Over.mk (T.hom ≫ b)))
    exact lam_eq (s := (snd G (Over.mk (T.hom ≫ b))).left ≫ T.hom) (s₀ := (G ⊗ Over.mk (T.hom ≫ b)).hom)
      hφ hL hL' e hs (trR hφ T ≫ fst G' T) (trR hφ T ≫ snd G' T ≫ y) (fst G (Over.mk (T.hom ≫ b)))
      (snd G (Over.mk (T.hom ≫ b)) ≫ pushP hφ (s := T.hom) rfl y)
      (by rw [Over.comp_left, Category.assoc]; exact trR_fst hφ T)
      (by simp only [Over.comp_left, Category.assoc, trR_snd_assoc]; rfl)
  obtain ⟨j, hj⟩ : ∃ j : (G' ⊗ T).left ⟶ (G ⊗ Over.mk (T.hom ≫ b)).left, j ≫ (trR hφ T).left = 𝟙 (G' ⊗ T).left :=
    ⟨_, trR_section hφ T⟩
  refine ⟨fun h ↦ key.symm.trans ?_, fun h ↦ ?_⟩
  · rw [h, map_zero]
  · have := congrArg (CechPic.pull j) (key.trans h)
    rwa [← pull_comp, hj, pull_id, map_zero] at this

end Transport

theorem exists_fg_fst_eq {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {X : Scheme.{0}} (p : X ⟶ Sp k)
    [QuasiCompact p] [LocallyOfFiniteType p] (e : Sp k ⟶ X) (he : e ≫ p = 𝟙 _)
    (h : pullback.fst p (spMap (algebraMap k V)) = pullback.fst p (spMap (algebraMap k V)) ≫ p ≫ e) :
    ∃ R : Subalgebra k V, R.FG ∧
      pullback.fst p (spMap (algebraMap k R)) = pullback.fst p (spMap (algebraMap k R)) ≫ p ≫ e := by
  obtain ⟨R, hle, hR, hab⟩ := GlobalTheory.Spread.exists_fg_comp_eq_comp p p (⊥ : Subalgebra k V) Subalgebra.fg_bot
    (pullback.fst _ _) (pullback.fst _ _ ≫ p ≫ e) rfl
    (by simp only [Category.assoc, he, Category.comp_id])
    (by simpa only [GlobalTheory.Spread.bcMap_fst, GlobalTheory.Spread.bcMap_fst_assoc] using h)
  refine ⟨R, hR, ?_⟩
  simpa only [GlobalTheory.Spread.bcMap_fst, GlobalTheory.Spread.bcMap_fst_assoc] using hab

section KTriv

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem kTriv_of_ker (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB)
    (H : ∀ (T : Over S) (y : T ⟶ A), Triv (ev (abelian₂ A L) (fst A T) (snd A T ≫ y)) → y = 1) : Out.KTriv A L := by
  intro R _ t x hx
  have := hA.comm
  refine H (Over.mk t) x ?_
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  have hM := pull_isLB hP (lift (fst A (Over.mk t)) (snd A (Over.mk t) ≫ x)).left
  have hcM : cls _ hM = lam (cls L hL) (fst A (Over.mk t)) (snd A (Over.mk t) ≫ x) := by
    rw [cls_ev hP, evc_lam hL]
  refine triv_of_section_of_locally_triv _ _ (snd A (Over.mk t)).left (lift (1 : Over.mk t ⟶ A) (𝟙 _)).left
    (by rw [lift_left_snd]; rfl) ?_ _ hM ?_ ?_
  · exact fun U ↦ isIso_app_of_isAbelianScheme _ ((Over.pullback t).obj A) (isAbelianScheme_pullback A hA t) U
  · refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, hcM, pull_lam, lift_fst, lam_one_left]
  · intro p₀
    obtain ⟨V, hV, hc⟩ := hx p₀
    obtain ⟨V', hV', hz⟩ := exists_pull_eq_zero
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : Over.mk t ⟶ A).left (cls L hL)) p₀
    refine ⟨V ⊓ V', ⟨hV, hV'⟩, (cls_eq_zero_iff (pull_isLB hM _)).1 ?_⟩
    have e₁ := pull_translDiff hL x hD (snd A (Over.mk t)) (fst A (Over.mk t))
    have e₂ : cls _ hM = CechPic.pull (lift (snd A (Over.mk t)) (fst A (Over.mk t))).left (cls _ hD) -
        CechPic.pull (snd A (Over.mk t)).left
          (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : Over.mk t ⟶ A).left (cls L hL)) := by
      rw [hcM, lam_comm, e₁, lam, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left,
        MonObj.comp_one]
      abel
    have z₁ : CechPic.pull ((fst (Over.mk t) A).left ⁻¹ᵁ V).ι (cls _ hD) = 0 := by
      rw [← cls_pull hD _ (pull_isLB hD _)]
      exact (cls_eq_zero_iff (pull_isLB hD _)).2 hc
    rw [cls_pull hM, e₂, map_sub, ← pull_comp, ← pull_comp]
    rw [pull_eq_zero_of_mem _ _ ?_ z₁, pull_eq_zero_of_mem V' _ ?_ hz, sub_zero]
    · exact fun z ↦ z.2.2
    · intro z
      have w : (lift (snd A (Over.mk t)) (fst A (Over.mk t))).left ≫ (fst (Over.mk t) A).left =
          (snd A (Over.mk t)).left := lift_left_fst _ _
      exact (congrArg (fun q ↦ q z.1 ∈ V) w).mpr z.2.1

end KTriv

theorem exists_model (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (L : LB A.left) (hL : L.IsLB) :
    ∃ (k : Type) (_ : CommRing k) (_ : IsNoetherianRing k) (_ : Algebra k R) (B : Over (Sp k)) (_ : GrpObj B)
      (φ : A.left ⟶ B.left) (M : LB B.left), IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧
        IsGrpPullback A B (spMap (algebraMap k R)) φ ∧ M.IsLB ∧ LBIso L (M.pull φ) := by
  obtain ⟨S, B, instB, φ, hS, hB, hφ, M, hM⟩ : ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B)
      (φ : A.left ⟶ B.left), Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧
        ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull φ) := by
    obtain ⟨S, B, instB, φ, M, h₁, h₂, h₃, h₄, h₅⟩ := exists_model_abelian_lb R A hA L hL
    exact ⟨S, B, instB, φ, h₁, h₂, h₃, M, h₄, h₅⟩
  obtain ⟨hMB, hLM⟩ := hM
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
  obtain ⟨instB₂, φ₁, hB₂, hAB₂, hc⟩ := model_passes_to_subalgebra S R A B φ hφ R'
  have : Algebra.FiniteType S R' := (Subalgebra.fg_iff_finiteType R').1 hR'fg
  refine ⟨R', inferInstance, Algebra.FiniteType.isNoetherianRing S R', inferInstance,
    Over.mk (pullback.snd B.hom (spMap (algebraMap S R'))), instB₂, φ₁, M.pull (pullback.fst _ _),
    isAbelianScheme_of_isGrpPullback _ hB₂ hB, hR', hAB₂, pull_isLB hMB _, ?_⟩
  have hM₁ := pull_isLB hMB (pullback.fst B.hom (spMap (algebraMap S R')))
  refine (cls_eq_iff hL (pull_isLB hM₁ φ₁)).1 ?_
  rw [(cls_eq_iff hL (pull_isLB hMB φ)).2 hLM, cls_pull hMB, cls_pull hM₁, cls_pull hMB, ← pull_comp, hc]

theorem kTrivModel_of_trivLocus : TrivLocus → KTrivModel := by
  intro hT R _ A _ g hA hg L hL hK
  have := hA.comm
  obtain ⟨k, _, _, _, B, _, φ, M, hB, hgB, hφ, hM, hLM⟩ := exists_model R A g hA hg L hL
  have := hB.smooth
  have := hB.proper
  have hBn : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have hN : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
  obtain ⟨Z, i, hic, hiT⟩ := hT (Sp k) B B hB hBn (abelian₂ B M) hN
    ((triv_ev_iff hN _ _).2 (by rw [evc_lam hM, lam_one_left]))
  obtain ⟨e, he⟩ := (hiT (𝟙_ _) 1).1 ((triv_ev_iff hN _ _).2 (by rw [evc_lam hM, MonObj.comp_one, lam_one_right]))
  have hZ : Z.hom = i.left ≫ B.hom := (Over.w i).symm
  have : QuasiCompact Z.hom := hZ ▸ inferInstance
  have : LocallyOfFiniteType Z.hom := hZ ▸ inferInstance

  have hzero : ∀ (T₀ : Over (Sp k)) (z : T₀ ⟶ Z), (z ≫ i).left = (1 : T₀ ⟶ B).left → z.left = T₀.hom ≫ e.left := by
    intro T₀ z hz
    have h1 : (toUnit T₀ ≫ e) ≫ i = 1 := by rw [Category.assoc, he, MonObj.comp_one]
    have h2 : (toUnit T₀ ≫ e).left = T₀.hom ≫ e.left := rfl
    rw [← h2]
    refine (cancel_mono i.left).1 ?_
    rw [← Over.comp_left, ← Over.comp_left, h1]
    exact hz

  have hpt : pullback.fst Z.hom (spMap (algebraMap k R)) =
      pullback.fst Z.hom (spMap (algebraMap k R)) ≫ Z.hom ≫ e.left := by
    let T : Over (Sp R) := Over.mk (pullback.snd Z.hom (spMap (algebraMap k R)))
    let T₀ : Over (Sp k) := Over.mk (T.hom ≫ spMap (algebraMap k R))
    let z : T₀ ⟶ Z := Over.homMk (pullback.fst Z.hom (spMap (algebraMap k R))) pullback.condition
    let y : T ⟶ A := liftPt hφ T.hom (z ≫ i).left (Over.w (z ≫ i))
    have hy : pushP hφ (s := T.hom) rfl y = z ≫ i := Over.OverMorphism.ext (liftPt_left _ _ _ _)
    have h1 : y = 1 := (isPerfect_lam hL hK).ker_right T y
      ((triv_lam_iff hφ hM hL hLM T y).2 (by rw [hy]; exact (hiT T₀ (z ≫ i)).2 ⟨z, rfl⟩))
    have h2 : (z ≫ i).left = (1 : T₀ ⟶ B).left := by
      rw [← congrArg (fun q ↦ q.left) hy]
      show y.left ≫ φ = _
      rw [h1]
      exact one_left_comp hφ rfl
    have h3 := hzero T₀ z h2
    have h4 : T₀.hom = pullback.fst Z.hom (spMap (algebraMap k R)) ≫ Z.hom := pullback.condition.symm
    rw [h4, Category.assoc] at h3
    exact h3
  obtain ⟨R₂, hfg, hR₂⟩ := exists_fg_fst_eq Z.hom e.left (Over.w e) hpt
  obtain ⟨instB₂, φ₁, hB₂, hAB₂, hc⟩ := GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra k R A B φ hφ R₂
  have : Algebra.FiniteType k R₂ := (Subalgebra.fg_iff_finiteType R₂).1 hfg
  have hM₂ := pull_isLB hM (pullback.fst B.hom (spMap (algebraMap k R₂)))
  have hab₂ : IsAbelianScheme (Over.mk (pullback.snd B.hom (spMap (algebraMap k R₂)))) :=
    isAbelianScheme_of_isGrpPullback _ hB₂ hB
  refine ⟨R₂, inferInstance, R₂.val.toRingHom, Over.mk (pullback.snd B.hom (spMap (algebraMap k R₂))), instB₂, φ₁,
    M.pull (pullback.fst _ _), Algebra.FiniteType.isNoetherianRing k R₂, hab₂, ?_, hAB₂, hM₂, ?_, ?_⟩
  · have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback B.hom (spMap (algebraMap k R₂))) hgB
  · refine kTriv_of_ker hab₂ hM₂ fun T y hy ↦ ?_
    have hy₀ := (triv_lam_iff hB₂ hM hM₂ ((cls_eq_iff hM₂ hM₂).1 rfl) T y).1 hy
    obtain ⟨z, hz⟩ := (hiT _ _).1 hy₀
    have h1 : z.left = (Over.mk (T.hom ≫ spMap (algebraMap k R₂))).hom ≫ e.left := by
      let l : T.left ⟶ pullback Z.hom (spMap (algebraMap k R₂)) := pullback.lift z.left T.hom (Over.w z)
      have hl : l ≫ pullback.fst _ _ = z.left := pullback.lift_fst _ _ _
      have := congrArg (l ≫ ·) hR₂
      simp only [reassoc_of% hl, hl] at this
      rw [this, ← Category.assoc, Over.w z]
    have h2 : y.left ≫ pullback.fst _ _ = (1 : Over.mk (T.hom ≫ spMap (algebraMap k R₂)) ⟶ B).left := by
      have e₁ := congrArg (fun q ↦ q.left) hz
      have e₂ : (toUnit (Over.mk (T.hom ≫ spMap (algebraMap k R₂))) ≫ e ≫ i) =
          (1 : Over.mk (T.hom ≫ spMap (algebraMap k R₂)) ⟶ B) := by rw [he, MonObj.comp_one]
      refine e₁.symm.trans ?_
      rw [Over.comp_left, h1, ← congrArg (fun q ↦ q.left) e₂]
      simp
    exact pt_ext hB₂ (h2.trans (one_left_comp hB₂ rfl).symm)
  · refine (cls_eq_iff hL (pull_isLB hM₂ φ₁)).1 ?_
    rw [(cls_eq_iff hL (pull_isLB hM φ)).2 hLM, cls_pull hM, cls_pull hM₂, cls_pull hM, ← pull_comp, hc]

end GlobalTheory.CompanionTheory.KTrivSpread
