import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.PolOpen

section
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem relAmple_pull_of_affine (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w)
    (hf : ∀ U' : S'.Opens, IsAffineOpen U' → ∃ U : S.Opens, IsAffineOpen U ∧ U' ≤ f ⁻¹ᵁ U) (hA : RelAmple A L) :
    RelAmple A' L' := by
  intro U' hU'
  obtain ⟨U, hU, le⟩ := hf U' hU'
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA U hU
  have le' : A'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy => (congrArg (fun q => q y ∈ U) h.w).mpr (le hy)
  let ψ := φ.resLE (A.hom ⁻¹ᵁ U) (A'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (A'.hom ∣_ U') (A.hom ∣_ U) (f.resLE U U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict A.hom U).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict A'.hom U').flip.paste_horiz h
    · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w, Category.assoc,
        Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine U := hU
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have hP' := linComb_isLB L' hL' (K := Fin N) (fun _ => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A' L' U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L U N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A' L' U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((f.resLE U U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end

theorem mem_abLocus_of_open {S S' : Scheme.{0}} (j : S' ⟶ S) [IsOpenImmersion j] (G : Over S) (s : S')
    (hs : s ∈ abLocus ((Over.pullback j).obj G)) : j s ∈ abLocus G := by
  rintro K _ _ t ⟨p, hp⟩
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hr : Set.range t ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    exact ⟨s, by rw [Subsingleton.elim q p, hp]⟩
  let t' := IsOpenImmersion.lift j t hr
  have ht : t' ≫ j = t := IsOpenImmersion.lift_fac _ _ _
  have hp' : t' p = s := j.isOpenEmbedding.injective ((congrArg (fun q => q p) ht).trans hp)
  have h₁ : IsProper (pullback.snd (pullback.snd G.hom j) t') := hs K t' ⟨p, hp'⟩
  have h₂ := (IsPullback.of_hasPullback (pullback.snd G.hom j) t').paste_horiz (IsPullback.of_hasPullback G.hom j)
  rw [ht] at h₂
  rw [← h₂.isoPullback_inv_snd]
  infer_instance

theorem polOnAb_open {S S' : Scheme.{0}} (j : S' ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (L : LB G.left)
    (hL : L.IsLB) (h : PolOnAb G L) : PolOnAb ((Over.pullback j).obj G) (L.pull (pullback.fst G.hom j)) := by
  intro W' hW'
  obtain ⟨ha, hK⟩ := h (j ''ᵁ W') (by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_abLocus_of_open j G s (hW' hs))
  have hr : Set.range (W'.ι ≫ j) ⊆ Set.range (j ''ᵁ W').ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  let e := IsOpenImmersion.lift (j ''ᵁ W').ι (W'.ι ≫ j) hr
  have he : e ≫ (j ''ᵁ W').ι = W'.ι ≫ j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (e ≫ (j ''ᵁ W').ι) := by rw [he]; infer_instance
  have : IsOpenImmersion e := IsOpenImmersion.of_comp e (j ''ᵁ W').ι
  have p₀ := isGrpPullback_pullback G (j ''ᵁ W').ι
  have p₁ := (isGrpPullback_pullback ((Over.pullback j).obj G) W'.ι).comp (isGrpPullback_pullback G j)
  have w₁ := p₁.1.w.trans ((congrArg _ he.symm).trans (Category.assoc _ _ _).symm)
  have p₂ := IsGrpPullback.cancel p₀ (p₁.congr he.symm (p₀.1.lift_fst _ _ w₁).symm) (p₀.1.lift_snd _ _ w₁)
  have hL₀ := pull_isLB hL (pullback.fst G.hom (j ''ᵁ W').ι)
  have hL₁ := pull_isLB (pull_isLB hL (pullback.fst G.hom j)) (pullback.fst ((Over.pullback j).obj G).hom W'.ι)
  obtain ⟨w, hw⟩ : LBIso ((L.pull (pullback.fst G.hom j)).pull (pullback.fst ((Over.pullback j).obj G).hom W'.ι))
      ((L.pull (pullback.fst G.hom (j ''ᵁ W').ι)).pull (p₀.1.lift _ _ w₁)) := by
    refine (CechPic.cls_eq_iff hL₁ (pull_isLB hL₀ _)).1 ?_
    rw [CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull hL, CechPic.cls_pull hL]
    exact (CechPic.pull_comp _ _ _).symm.trans ((congrArg (fun q => CechPic.pull q _) (p₀.1.lift_fst _ _ w₁).symm).trans
      (CechPic.pull_comp _ _ _))
  exact ⟨relAmple_pull_of_affine p₂.1 hL₀ hL₁ ((isGen_iff w).1 hw)
    (fun U' hU' => ⟨e ''ᵁ U', hU'.image_of_isOpenImmersion e, fun y hy => ⟨y, hy, rfl⟩⟩) ha,
    kTriv_pull p₂ hL₀ hL₁ ((isGen_iff w).1 hw) hK⟩

theorem polOnAb_affine : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (W : S.Opens) (hW : IsAffineOpen W),
    IsOpen (abLocus G) → PolOnAb G L.L → PolOnAb (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec).L :=
  fun _ G _ _ L _ hW _ h => polOnAb_open hW.fromSpec G L.L L.isLB h

end GlobalTheory.KeyVals.PolOpen

end
