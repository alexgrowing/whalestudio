import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIsPerfectOfAdditive

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.Model

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_ev {U T : Over S} {M : LB (A ⊗ U).left} (h : Fam A M) (u : T ⟶ U) :
    Fam A (ev M (fst A T) (snd A T ≫ u)) := by
  have hM : (ev M (fst A T) (snd A T ≫ u)).IsLB := pull_isLB h.isLB _
  refine ⟨hM, (isAdditive_iff hM).2 fun Y a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Y a a' _

theorem rep_ext {B S' Y : Over S} {b : B ⟶ S'} {P : LB (A ⊗ B).left} (h : Rep A b P) {u u' : Y ⟶ B}
    (hb : u ≫ b = u' ≫ b) (e : Same A P P u u') : u = u' := by
  have hu := fam_ev h.fam u
  exact (h.univ Y (u ≫ b) _ hu).unique ⟨rfl, (cls_eq_iff hu.isLB hu.isLB).1 rfl⟩ ⟨hb.symm, e⟩

theorem isChart_of_rep {B : Over S} {P : LB (A ⊗ B).left} (h : Rep A (toUnit B) P) : IsChart A P where
  fam := h.fam
  inj _ _ _ e := rep_ext h (toUnit_unique _ _) e
  chart T N hN := ⟨⊤, fun Y y ↦ ⟨fun _ _ ↦ trivial, fun _ ↦ by
    obtain ⟨x, hx, -⟩ := h.univ Y (toUnit Y) _ (fam_ev hN y)
    exact ⟨x, hx.2⟩⟩⟩

theorem rep_baseChange {B : Over S} {P : LB (A ⊗ B).left} (h : Rep A (toUnit B) P) (S' : Over S) :
    Rep A (snd B S') (ev P (fst A _) (snd A _ ≫ fst B S')) where
  fam := fam_ev h.fam _
  univ T t N hN := by
    have hQ := (fam_ev h.fam (fst B S')).isLB
    have key : ∀ y : T ⟶ B ⊗ S', LBIso N (ev (ev P (fst A _) (snd A _ ≫ fst B S')) (fst A T) (snd A T ≫ y)) ↔
        LBIso N (ev P (fst A T) (snd A T ≫ y ≫ fst B S')) := fun y ↦ by
      rw [← cls_eq_iff hN.isLB (pull_isLB hQ _), ← cls_eq_iff hN.isLB (pull_isLB h.fam.isLB _), cls_ev hQ,
        cls_ev h.fam.isLB, evc_ev h.fam.isLB, lift_fst, lift_snd_assoc, Category.assoc]
    obtain ⟨x, hx, hu⟩ := h.univ T (toUnit T) N hN
    refine ⟨lift x t, ⟨lift_snd _ _, (key _).2 (by rw [lift_fst]; exact hx.2)⟩, fun y hy ↦ ?_⟩
    ext1
    · rw [lift_fst]
      exact hu _ ⟨toUnit_unique _ _, (key y).1 hy.2⟩
    · rw [lift_snd, hy.1]

theorem liftAt_baseChange {g : ℕ} {B : Over S} {P : LB (A ⊗ B).left} (h : Fam A P)
    (hg : SmoothOfRelativeDimension g B.hom) (S' : Over S) (x : (B ⊗ S').left) :
    LiftAt A g (snd B S') (ev P (fst A _) (snd A _ ≫ fst B S')) x := by
  refine ⟨B, P, 𝟙 _, h, hg, Category.id_comp _, inferInstanceAs (IsOpenImmersion (𝟙 (B ⊗ S').left)), ⟨x, rfl⟩, ?_⟩
  rw [same_iff h.isLB (fam_ev h (fst B S')).isLB, evc_ev h.isLB, lift_fst, lift_snd_assoc, Category.comp_id]

theorem good_snd {g : ℕ} {B : Over S} (h : Good g B.hom) (S' : Over S) : Good g (snd B S').left := by
  have H : IsPullback (fst B S').left (snd B S').left B.hom S'.hom := IsPullback.of_hasPullback _ _
  have := smoothOfRelativeDimension_isStableUnderBaseChange g
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) H h.proper,
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) H h.smooth,
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) H h.conn⟩

theorem hasRep_of_dual (H : GlobalTheory.Published.DualAbelianScheme) (hA : IsAbelianScheme A) {g : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) (S' : Over S) : HasRep A g S' := by
  obtain ⟨B, _, P, hB, hd, h, -⟩ := H S A hA
  exact ⟨_, _, _, rep_baseChange (Rep.of_isDual h) S', good_snd ⟨hB.proper, hd g hg, hB.geomConnected⟩ S'⟩

theorem hasRepAF_unit (S' : Over S) [IsAffine S'.left] : HasRepAF (𝟙_ (Over S)) 0 S' := by
  have r := rep_baseChange (Rep.of_isDual (isDual_unit (S := S))) S'
  have g : Good 0 (snd (𝟙_ (Over S)) S').left :=
    good_snd (show Good 0 (𝟙 S) from ⟨inferInstance, inferInstance, inferInstance⟩) S'
  refine ⟨_, _, _, r, g, fun F ↦ ⟨⊤, ?_, fun _ _ ↦ trivial⟩⟩
  have : IsIso (λ_ S').hom.left := (Over.forget _).map_isIso (λ_ S').hom
  have : IsAffine (𝟙_ (Over S) ⊗ S').left := .of_isIso (λ_ S').hom.left
  exact isAffineOpen_top _

theorem isIso_of_rep_unit {B S' : Over S} {b : B ⟶ S'} {P : LB (𝟙_ (Over S) ⊗ B).left}
    (h : Rep (𝟙_ (Over S)) b P) : IsIso b := by
  have z : ∀ (Y : Over S) (a : Y ⟶ 𝟙_ (Over S)) (u : Y ⟶ B), evc h.fam.isLB a u = 0 := fun Y a u ↦ by
    rw [toUnit_unique a 1]
    exact h.fam.add.evc_one h.fam.isLB u
  obtain ⟨x, hx, -⟩ := h.univ S' (𝟙 _) (LB.triv _) ⟨LB.isLB_triv _,
    (isAdditive_iff (LB.isLB_triv _)).2 fun _ _ _ _ ↦ by
      have h0 : ∀ (Y : Over S) (a : Y ⟶ 𝟙_ (Over S)) (t : Y ⟶ S'), evc (LB.isLB_triv _) a t = 0 :=
        fun _ _ _ ↦ map_zero _
      simp only [h0, add_zero]⟩
  refine ⟨x, rep_ext h (by rw [Category.assoc, hx.1, Category.comp_id, Category.id_comp]) ?_, hx.1⟩
  rw [same_iff h.fam.isLB h.fam.isLB, z, z]

theorem eq_zero_of_hasRep_unit {g : ℕ} {S' : Over S} (hS : Nonempty S'.left) (h : HasRep (𝟙_ (Over S)) g S') :
    g = 0 := by
  obtain ⟨B, b, P, hr, hg⟩ := h
  have := isIso_of_rep_unit hr
  have : IsIso b.left := (Over.forget _).map_isIso b
  let f : 𝟙_ (Over S'.left) ⟶ Over.mk b.left := Over.homMk (inv b.left) (IsIso.inv_hom_id _)
  have : IsIso ((Over.forget _).map f) := inferInstanceAs (IsIso (inv b.left))
  exact (GlobalTheory.relDim_unique_of_iso_grp _ hS _ _ f (isIso_of_reflects_iso f (Over.forget _)) 0 g
    (inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 S'.left))) hg.smooth).symm

theorem inj_of_isPerfect {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (h : IsPerfect A B P)
    (ha : IsAdditive (swap P)) : Inj A P := fun Y u u' e ↦ by
  have hs : (swap P).IsLB := pull_isLB h.isLB _
  have e' := (same_iff h.isLB h.isLB _ _).1 e
  have a := (isAdditive_iff hs).1 ha _ (snd A Y ≫ (u * u'⁻¹)) (snd A Y ≫ u') (fst A Y)
  rw [← MonObj.comp_mul, inv_mul_cancel_right, evc_swap h.isLB, evc_swap h.isLB, evc_swap h.isLB, e'] at a
  have t := h.ker_right Y (u * u'⁻¹) ((triv_ev_iff h.isLB _ _).2 (right_eq_add.1 a))
  rwa [mul_inv_eq_one] at t

omit [GrpObj A] in

theorem fibInj_of_inj {U : Over S} {M : LB (A ⊗ U).left} (h : Inj A M) : FibInj A M :=
  fun _ _ _ _ Y _ u u' e ↦ h Y u u' e

omit [GrpObj A] in

theorem eq_of_inj_triv {U Y : Over S} (h : Inj A (LB.triv (A ⊗ U).left)) (u u' : Y ⟶ U) : u = u' :=
  h Y u u' ((same_iff (LB.isLB_triv _) (LB.isLB_triv _) _ _).2 ((map_zero _).trans (map_zero _).symm))

omit [GrpObj A] in

theorem dimLe_self : DimLe A A := fun _ _ _ h ↦ h

theorem ell {R : Type} [CommRing R] [IsNoetherianRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    haveI := (WeierstrassCurve.ellPolAV W).isAb.comm
    Fam (WeierstrassCurve.ellPolAV W).A (abelian₂ _ (WeierstrassCurve.ellPolAV W).L) ∧
      Inj (WeierstrassCurve.ellPolAV W).A (abelian₂ _ (WeierstrassCurve.ellPolAV W).L) ∧
      Good 1 (WeierstrassCurve.ellPolAV W).A.hom := by
  have hA := (WeierstrassCurve.ellPolAV W).isAb
  have h := isPerfect_ell W
  exact ⟨⟨h.isLB, CubeNoeth.isAdditive_of_triv_axes hA hA h.isLB h.zero_left h.zero_right⟩,
    inj_of_isPerfect h (CubeNoeth.isAdditive_swap_of_triv_axes hA hA h.isLB h.zero_left h.zero_right),
    hA.proper, (WeierstrassCurve.ellPolAV W).smoothDim, hA.geomConnected⟩

theorem ell_rep (H : GlobalTheory.Published.DualAbelianScheme) {R : Type} [CommRing R] [IsNoetherianRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    haveI := (WeierstrassCurve.ellPolAV W).isAb.comm
    Rep (WeierstrassCurve.ellPolAV W).A (toUnit _) (abelian₂ _ (WeierstrassCurve.ellPolAV W).L) ∧
      IsChart (WeierstrassCurve.ellPolAV W).A (abelian₂ _ (WeierstrassCurve.ellPolAV W).L) := by
  have hA := (WeierstrassCurve.ellPolAV W).isAb
  have r := Rep.of_isDual (GlobalTheory.PerfectDual.isDual_of_isPerfect H _ _ hA hA (WeierstrassCurve.ellPolAV W).smoothDim
    (WeierstrassCurve.ellPolAV W).smoothDim (isPerfect_ell W))
  exact ⟨r, isChart_of_rep r⟩

theorem same_unit {T U Y : Over S} {N : LB (𝟙_ (Over S) ⊗ T).left} {M : LB (𝟙_ (Over S) ⊗ U).left}
    (hN : Fam (𝟙_ (Over S)) N) (hM : Fam (𝟙_ (Over S)) M) (y : Y ⟶ T) (u : Y ⟶ U) :
    Same (𝟙_ (Over S)) N M y u := by
  rw [same_iff hN.isLB hM.isLB, toUnit_unique (fst _ Y) 1, hN.add.evc_one hN.isLB, hM.add.evc_one hM.isLB]

theorem isChart_unit_iff {U : Over S} {M : LB (𝟙_ (Over S) ⊗ U).left} (hM : Fam (𝟙_ (Over S)) M) :
    IsChart (𝟙_ (Over S)) M ↔ IsOpenImmersion U.hom := by
  constructor
  · intro h
    obtain ⟨W, hW⟩ := h.chart (𝟙_ _) _ (Rep.of_isDual isDual_unit).fam
    have F := (Rep.of_isDual (isDual_unit (S := S))).fam
    obtain ⟨u, -⟩ := (hW (Over.mk W.ι) (toUnit _)).2 fun z ↦ z.2
    have m : ∀ z, U.hom z ∈ W := (hW U (toUnit _)).1 ⟨𝟙 _, same_unit F hM _ _⟩
    let W' : S.Opens := W
    let l : U.left ⟶ W' := IsOpenImmersion.lift W'.ι U.hom (by
      rintro _ ⟨z, rfl⟩; rw [Scheme.Opens.range_ι]; exact m z)
    have hl : l ≫ W'.ι = U.hom := IsOpenImmersion.lift_fac _ _ _
    let l' : U ⟶ Over.mk W'.ι := Over.homMk l hl
    have e₁ : l' ≫ u = 𝟙 U := h.inj _ _ _ (same_unit hM hM _ _)
    have e₂ : u.left ≫ l = 𝟙 _ := by
      rw [← cancel_mono W'.ι, Category.assoc, hl, Over.w u]
      exact (Category.id_comp _).symm
    have : IsIso l := ⟨u.left, congrArg (fun q ↦ q.left) e₁, e₂⟩
    rw [← hl]
    infer_instance
  · intro h
    refine ⟨hM, fun Y u u' _ ↦ Over.OverMorphism.ext ?_, fun T N hN ↦
      ⟨T.hom ⁻¹ᵁ U.hom.opensRange, fun Y y ↦ ⟨?_, fun k ↦ ?_⟩⟩⟩
    · rw [← cancel_mono U.hom, Over.w, Over.w]
    · rintro ⟨u, -⟩ z
      refine ⟨u.left z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w, Over.w]
    · refine ⟨Over.homMk (IsOpenImmersion.lift U.hom Y.hom ?_) (IsOpenImmersion.lift_fac _ _ _),
        same_unit hN hM _ _⟩
      rintro _ ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := k z
      exact ⟨w, by rw [hw, ← Scheme.Hom.comp_apply, Over.w]⟩

theorem isChart_open {U V : Over S} {M : LB (A ⊗ U).left} (h : IsChart A M) (j : V ⟶ U) [IsOpenImmersion j.left] :
    IsChart A (ev M (fst A V) (snd A V ≫ j)) := by
  have hM := h.fam.isLB
  have hV := fam_ev h.fam j
  have key : ∀ {T Y : Over S} {N : LB (A ⊗ T).left} (_ : N.IsLB) (y : Y ⟶ T) (v : Y ⟶ V),
      Same A N (ev M (fst A V) (snd A V ≫ j)) y v ↔ Same A N M y (v ≫ j) := fun hN y v ↦ by
    rw [same_iff hN hV.isLB, same_iff hN hM, evc_ev hM, lift_fst, lift_snd_assoc, Category.assoc]
  have comp : ∀ {T Y Z : Over S} {N : LB (A ⊗ T).left} (_ : N.IsLB) {y : Y ⟶ T} {u : Y ⟶ U} (z : Z ⟶ Y),
      Same A N M y u → Same A N M (z ≫ y) (z ≫ u) := fun {T Y Z N} hN {y u} z e ↦ by
    have e' := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM _ _).1 e)
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc, Category.assoc, Category.assoc] at e'
    exact (same_iff hN hM _ _).2 e'
  refine ⟨hV, fun Y v v' e ↦ ?_, fun T N hN ↦ ?_⟩
  · have e' := (same_iff hV.isLB hM _ _).1 ((key hV.isLB _ _).1 e)
    rw [evc_ev hM, lift_fst, lift_snd_assoc, Category.assoc] at e'
    have := h.inj Y _ _ ((same_iff hM hM _ _).2 e')
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono j.left, ← Over.comp_left, this, Over.comp_left]
  · obtain ⟨W, hW⟩ := h.chart T N hN
    let w : Over.mk (W.ι ≫ T.hom) ⟶ T := Over.homMk W.ι rfl
    obtain ⟨u₀, h₀⟩ := (hW _ w).2 fun z ↦ z.2
    have lf : ∀ (Y : Over S) (y : Y ⟶ T), (∀ z, y.left z ∈ W) → ∃ y' : Y ⟶ Over.mk (W.ι ≫ T.hom), y' ≫ w = y :=
      fun Y y k ↦ by
      have r : Set.range y.left ⊆ Set.range W.ι := by
        rintro _ ⟨z, rfl⟩; rw [Scheme.Opens.range_ι]; exact k z
      refine ⟨Over.homMk (IsOpenImmersion.lift W.ι y.left r) ?_, Over.OverMorphism.ext ?_⟩
      · exact (IsOpenImmersion.lift_fac_assoc _ _ _ _).trans (Over.w y)
      · exact IsOpenImmersion.lift_fac _ _ _
    refine ⟨W.ι ''ᵁ (u₀.left ⁻¹ᵁ j.left.opensRange), fun Y y ↦ ⟨?_, fun k ↦ ?_⟩⟩
    · rintro ⟨v, hv⟩ z
      have hv' := (key hN.isLB _ _).1 hv
      obtain ⟨y', rfl⟩ := lf Y y ((hW Y y).1 ⟨_, hv'⟩)
      have e : v ≫ j = y' ≫ u₀ := h.inj _ _ _ ((same_iff hM hM _ _).2
        (((same_iff hN.isLB hM _ _).1 hv').symm.trans ((same_iff hN.isLB hM _ _).1 (comp hN.isLB y' h₀))))
      refine ⟨y'.left z, ⟨v.left z, ?_⟩, rfl⟩
      exact congrArg (fun q : Y ⟶ U ↦ q.left z) e
    · obtain ⟨y', rfl⟩ := lf Y y fun z ↦ by
        obtain ⟨p, -, hp⟩ := k z
        exact hp ▸ p.2
      have r : Set.range (y' ≫ u₀).left ⊆ Set.range j.left := by
        rintro _ ⟨z, rfl⟩
        obtain ⟨p, hp, e⟩ := k z
        obtain rfl : p = y'.left z := W.ι.isOpenEmbedding.injective e
        exact hp
      let v : Y ⟶ V := Over.homMk (IsOpenImmersion.lift j.left _ r) (by
        rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w])
      have hv : v ≫ j = y' ≫ u₀ := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
      exact ⟨v, (key hN.isLB _ _).2 (hv ▸ comp hN.isLB y' h₀)⟩

theorem not_dimLe_unit_ell {R : Type} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ¬ DimLe (WeierstrassCurve.ellPolAV W).A (𝟙_ _) := fun h ↦ by
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  have k := h 1 _ (𝟙 _) (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
    (IsPullback.of_hasPullback _ _) (WeierstrassCurve.ellPolAV W).smoothDim)
  refine one_ne_zero (eq_zero_of_hasRep_unit (S := Sp R) (g := 1) (S' := 𝟙_ _)
    (inferInstanceAs (Nonempty (PrimeSpectrum R))) ⟨_, _, _, rep_baseChange (Rep.of_isDual isDual_unit) _, ?_⟩)
  have z : Good 0 (snd (𝟙_ (Over (Sp R))) (𝟙_ _)).left :=
    good_snd (show Good 0 (𝟙 (Sp R)) from ⟨inferInstance, inferInstance, inferInstance⟩) _
  exact ⟨z.proper, k, z.conn⟩

theorem not_rep_ell_unit {R : Type} [CommRing R] [IsNoetherianRing R] [Nontrivial R] (W : WeierstrassCurve R)
    [W.IsElliptic] (P : LB ((WeierstrassCurve.ellPolAV W).A ⊗ 𝟙_ _).left) :
    ¬ Rep (WeierstrassCurve.ellPolAV W).A (toUnit _) P := fun h ↦ by
  obtain ⟨hf, hi, hg⟩ := ell W
  obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ _ (toUnit _) _ hf
  have c := (cls_eq_iff hf.isLB (pull_isLB h.fam.isLB _)).2 hx
  have e : (𝟙 (WeierstrassCurve.ellPolAV W).A) = 1 := hi _ _ _ <| (same_iff hf.isLB hf.isLB _ _).2 <| by
    rw [evc, evc, c, cls_ev h.fam.isLB, pull_evc, pull_evc, lift_fst, lift_fst]
    congr 1
    exact toUnit_unique _ _
  have : IsIso (toUnit (WeierstrassCurve.ellPolAV W).A) := ⟨1, by rw [MonObj.comp_one, e], toUnit_unique _ _⟩
  exact one_ne_zero (GlobalTheory.relDim_unique_of_iso_grp _ (inferInstanceAs (Nonempty (PrimeSpectrum R))) _ _
    (toUnit (WeierstrassCurve.ellPolAV W).A) this 1 0 hg.smooth
    (inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 (Sp R)))))

end GlobalTheory.DualCon.Model
