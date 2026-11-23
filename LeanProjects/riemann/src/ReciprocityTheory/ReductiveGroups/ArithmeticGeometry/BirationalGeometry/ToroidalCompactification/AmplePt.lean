import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1

section

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gen_chartPull {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (t : LB.Gen A) (ht : t.IsGen) :
    ∃ t' : LB.Gen A', t'.IsGen := by
  refine ⟨⟨fun i => res (a.le i) (pullU h _ (t.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := (gm_res h y _ hm _).symm.trans ((congrArg (gm h y _) (ht (a.idx i) (a.idx j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res h y _ hm _))))
  exact ((gm_res _ y _ hy _).trans (gm_rp₁ h y _ _ (a.le i) hy.1 _)).trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2) ((gm_res _ y _ hy _).trans (gm_rp₁ h y _ _ (a.le j) hy.2 _)))).symm)

def chartPullIn (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) :
    ChartPull (LB.LinComb L (fun k => h ≫ φ k) ε) ((LB.LinComb L φ ε).pull h) (𝟙 Y') :=
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull h).U (fun _ => j) := fun j y hy =>
    (mem_pull (L := LB.LinComb L φ ε)).2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  { idx := fun j _ => j
    le := le
    g := fun y j j' hj hj' => ((chartPullSame L _ φ ε h fun _ => rfl).g y j j' hj hj').trans
      ((gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y _ _ (le j hj) (le j' hj')).trans (by rw [Category.id_comp]; rfl)).symm }

def chartPullOut (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (ψ : K → (Y' ⟶ X)) (e : ∀ k, ψ k = h ≫ φ k) :
    ChartPull ((LB.LinComb L φ ε).pull h) (LB.LinComb L ψ ε) (𝟙 Y') := by
  obtain rfl : ψ = fun k => h ≫ φ k := funext e
  exact
    have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull h).U J ≤ LB.wchart L (fun k => h ≫ φ k) (J PUnit.unit) :=
      fun J y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 ((mem_pull (L := LB.LinComb L φ ε)).1 hy) k
    { idx := fun J => J PUnit.unit
      le := le
      g := fun y J J' hj hj' => ((gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y J J' hj hj').trans (by rw [Category.id_comp]; rfl)).trans
        ((chartPullSame L _ φ ε h fun _ => rfl).g y _ _ (le J hj) (le J' hj')).symm }

theorem iso_linComb {w : LB.Iso L' (L.pull F)} (hw : PGen w) (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) :
    LBIso (LB.LinComb L' φ' ε) (LB.LinComb L (fun k => φ' k ≫ F) ε) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  refine ⟨⟨fun p => u p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans ((hu _ _ _ (𝟙 Y') y hy.1).trans (pw_trans hw φ' ε (𝟙 Y') y hy.1.1 hy.2.1 hy.1.2 hy.2.2))).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div _ _ (𝟙 Y') y p q hy).trans ?_)
      ((gm_res _ y _ hy _).trans (hu _ _ _ (𝟙 Y') y hy.2)))))
  exact congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L _ ε (𝟙 Y') y p.1 q.1 hy.1.1 hy.2.1)
    (gm_linComb L' φ' ε (𝟙 Y') y p.2 q.2 hy.1.2 hy.2.2)

theorem mem_nonzeroLocus {M : LB Y} (s : LB.Sec M) (y : Y) :
    y ∈ nonzeroLocus s ↔ ∃ k, y ∈ M.U k ∧ IsUnit (gs (𝟙 Y) y _ (s.f k)) := by
  simp only [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]
  refine exists_congr fun k => ?_
  constructor
  · intro hy
    have hk : y ∈ M.U k := Scheme.basicOpen_le _ _ hy
    refine ⟨hk, ?_⟩
    have hu := (Scheme.mem_basicOpen Y (s.f k) y hk).1 hy
    unfold gs
    rw [dif_pos (show (𝟙 Y : Y ⟶ Y) y ∈ M.U k by simpa using hk)]
    exact hu
  · rintro ⟨hk, hu⟩
    unfold gs at hu
    rw [dif_pos (show (𝟙 Y : Y ⟶ Y) y ∈ M.U k by simpa using hk)] at hu
    exact (Scheme.mem_basicOpen Y (s.f k) y hk).2 hu

end

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem kTriv_pull (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull φ)} (hw : PGen w)
    (hK : KTriv A L) : KTriv A' L' := by
  intro R _ t x hx
  have inj : ∀ {T : Over S'} {x y : T ⟶ A'}, pushPt h.1.w x = pushPt h.1.w y → x = y := fun {T x y} e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
  refine inj ((hK R (t ≫ f) (pushPt h.1.w x) fun p => ?_).trans (map_one (pushHom h (Over.mk t))).symm)
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let T : Over S := Over.mk (t ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ t)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ t) ≫ f := pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ Over.mk t := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₁ : (lift a b).left ≫ (fst (Over.mk t) A').left = (fst T A).left := congrArg (fun q => q.left) (lift_fst a b)
  have k₂ : (lift a b).left ≫ (snd (Over.mk t) A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst (Over.mk t) A' ≫ x) * snd (Over.mk t) A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst (Over.mk t) A' ≫ x) * snd (Over.mk t) A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨n, hn⟩ : ∃ n : ((fst T A).left ⁻¹ᵁ V).toScheme ⟶ ((fst (Over.mk t) A').left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst (Over.mk t) A').left ⁻¹ᵁ V).ι = ((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left :=
    ⟨IsOpenImmersion.lift _ (((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L' _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ φ = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]

omit [GrpObj A] [GrpObj A'] in
theorem relAmple_pull (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull φ)}
    (hw : PGen w) (U : S.Opens) (hU : IsAffineOpen U) (hf : ∀ y, f y ∈ U) (hA : RelAmple A L) : RelAmple A' L' := by
  intro U' hU'
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA U hU
  have le : U' ≤ f ⁻¹ᵁ U := fun y _ => hf y
  have le' : A'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y _ => (congrArg (fun q => q y ∈ U) h.w).mpr (hf _)
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

theorem amplePt : AmplePtSt := by
  intro S K _ f A A' _ _ φ h L L' hL hL' ⟨w, hw⟩ hA hK
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f (default : PrimeSpectrum K)) trivial
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact ⟨relAmple_pull h.1 hL hL' ((isGen_iff w).1 hw) U hU (fun y => by rwa [Subsingleton.elim y (default : PrimeSpectrum K)]) hA,
    kTriv_pull h hL hL' ((isGen_iff w).1 hw) hK⟩

theorem thetaCore_of (hT : SecTwistSt) : ThetaCoreSt := thetaCore hT amplePt

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
