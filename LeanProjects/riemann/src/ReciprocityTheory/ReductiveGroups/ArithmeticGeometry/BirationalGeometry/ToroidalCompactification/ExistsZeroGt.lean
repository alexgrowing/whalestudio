import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem prod_gt (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφ D F b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  simp [DegPre.gtφ, DegPre.gtε] <;> rfl

theorem cPoint_zero (T : Over (Spec (CommRingCat.of R))) : cP D T 0 = 1 := by
  have h0 : D.c 0 = 1 := by
    have e := D.c_add 0 0
    rw [add_zero] at e
    have e' : D.c 0 * D.c 0 = D.c 0 * 1 := by
      rw [_root_.mul_one]
      exact e.symm
    exact _root_.mul_left_cancel e'
  unfold cP
  rw [h0]
  first
  | simp
  | (rw [Hom.one_def, Hom.one_def, ← Category.assoc]
     congr 1
     exact toUnit_unique _ _)

theorem val_cubAt {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) (x x' w : TF (R := R) F ⟶ D.P.A) :
    val (DegPre.cubAt D F x x' w) (𝟙 _) y J = th D y J x x' w := by
  unfold DegPre.cubAt
  refine (val_pull (hJ := hJ) ..).trans ?_
  rw [Category.id_comp]
  rfl

theorem exists_gt (b : TF (R := R) F ⟶ D.P.A) {K : Type} [Fintype K] {φ : D.X → K → ((TF (R := R) F).left ⟶ D.P.A.left)}
    {ε : K → ℤ} (v : ∀ χ, LB.Gen (LB.LinComb D.P.L (φ χ) ε)) (hv : ∀ χ, (v χ).IsGen)
    (hF : ∀ χ, FormEq (φ χ) ε (DegPre.gtφ D F b χ) DegPre.gtε)
    (h₀ : ∀ y J, Good D.P.L y J → val (v 0) (𝟙 _) y J = 1)
    (hm : ∀ χ χ' y J, Good D.P.L y J → val (v (χ + χ')) (𝟙 _) y J * th D y J (cP D _ χ) (cP D _ χ') b =
      val (v χ) (𝟙 _) y J * val (v χ') (𝟙 _) y J) :
    ∃ g : GtPtF D F, g.b = b ∧ ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = val (v χ) (𝟙 _) y J := by
  choose s hs hsv using fun χ => exists_gen D.P.isLB (hF χ) (v χ) (hv χ)
  refine ⟨{ b := b, s := s, isGen := hs, s_zero := ?_, mult := ?_ }, rfl, ?_⟩
  · refine corr_of_val D.P.isLB (fun y J hy => ?_)
    refine (hsv 0 _ (𝟙 _) y J hy).trans ?_
    exact (h₀ y J hy).trans (val_one _).symm
  · intro χ χ'
    refine corr_of_val D.P.isLB (fun y J hy => ?_)
    refine (val_mul (hJ := hy) ..).trans ?_
    refine Eq.trans ?_ (val_mul (hJ := hy) ..).symm
    rw [val_cubAt hy, hsv (χ + χ') _ (𝟙 _) y J hy, hsv χ _ (𝟙 _) y J hy, hsv χ' _ (𝟙 _) y J hy]
    exact hm χ χ' y J hy
  · intro χ y J hy
    exact hsv χ _ (𝟙 _) y J hy

theorem isAdd_iff (g g' g'' : GtPtF D F) : g.IsAdd g' g'' ↔ g''.b = g.b * g'.b ∧ ∀ χ y J, Good D.P.L y J →
    val (g''.s χ) (𝟙 _) y J * th D y J (cP D _ χ) g.b g'.b = val (g.s χ) (𝟙 _) y J * val (g'.s χ) (𝟙 _) y J := by
  constructor
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ y J hy => ?_⟩
    rw [← val_cubAt hy]
    refine (val_mul (hJ := hy) ..).symm.trans ?_
    refine (val_corr (hJ := hy) (hs χ) _).trans ?_
    exact val_mul (hJ := hy) ..
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ => corr_of_val D.P.isLB (fun y J hy => ?_)⟩
    refine (val_mul (hJ := hy) ..).trans ?_
    refine Eq.trans ?_ (val_mul (hJ := hy) ..).symm
    rw [val_cubAt hy]
    exact hs χ y J hy

theorem isZero_iff (g : GtPtF D F) : g.IsZero ↔ g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = 1 := by
  constructor
  · rintro ⟨hb, hs⟩
    exact ⟨hb, fun χ y J hy => (val_corr (hJ := hy) (hs χ) (𝟙 _)).trans (val_one _)⟩
  · rintro ⟨hb, hs⟩
    exact ⟨hb, fun χ => corr_of_val D.P.isLB (fun y J hy => (hs χ y J hy).trans (val_one _).symm)⟩

theorem isIota_iff (x : D.X) (g : GtPtF D F) : GtPtF.IsIota x g ↔ g.b = cP D _ x ∧ ∀ χ y J, Good D.P.L y J →
    val (g.s χ) (𝟙 _) y J = val (D.tau x χ) (𝟙 _ ≫ jFK (R := R) F) y J := by
  constructor
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ y J hy => ?_⟩
    refine (val_corr (hJ := hy) (hs χ) _).trans ?_
    exact val_pull (hJ := hy) ..
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ => corr_of_val D.P.isLB (fun y J hy => ?_)⟩
    refine (hs χ y J hy).trans ?_
    exact (val_pull (hJ := hy) ..).symm

private lemma th_eq_one' {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J)
    (x x' : TF (R := R) F ⟶ D.P.A) : th D y J x x' 1 = 1 := by
  have hm : lift x (lift x' 1) = lift x x' ≫ faceMap (G := D.P.A) 2 := by
    simp [faceMap, x2, pzero, Hom.one_def]
  refine Eq.trans ?_ ((val_corr (hJ := hJ) (D.cub.face 2) (lift x x').left).trans (val_one _))
  refine Eq.trans ?_ (val_pull (hJ := hJ) ..).symm
  show val D.cub.t (lift x (lift x' 1)).left y J = _
  rw [hm, Over.comp_left]
  all_goals rfl

theorem exists_zero_gt : ∃ g : GtPtF D F, g.IsZero := by
  have hgen : (LB.oneGen D.P.L (Y := (TF (R := R) F).left)).IsGen := by
    intro i j
    first
    | exact (_root_.one_mul _).symm
    | (simp only [LB.oneGen, LB.LinComb, Finset.univ_eq_empty, Finset.prod_empty]
       exact (_root_.one_mul _).symm)
    | (simp [LB.oneGen, LB.LinComb]
       rw [_root_.one_mul])
  obtain ⟨g, hb, hg⟩ := exists_gt (D := D) (F := F) (1 : TF (R := R) F ⟶ D.P.A) (K := PEmpty)
    (φ := fun _ => PEmpty.elim) (ε := PEmpty.elim) (fun _ => LB.oneGen D.P.L) (fun _ => hgen)
    (fun χ => by
      intro U _ h
      rw [prod_gt]
      simp)
    (fun y J _ => val_one _)
    (fun χ χ' y J hy => by
      rw [th_eq_one' hy]
      congr 1
      exact (val_one _).symm)
  exact ⟨g, (isZero_iff g).2 ⟨hb, fun χ y J hy => (hg χ y J hy).trans (val_one _)⟩⟩

theorem qk_equiv_refl (hB : D.TauBimult) {k : ℕ} (q : QkPt D F k) : QkPt.Equiv D F q q := by
  obtain ⟨h, hh⟩ := exists_zero_gt (D := D) (F := F)
  obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
  refine ⟨0, by simp, h, (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩,
    (isAdd_iff _ _ _).2 ⟨by rw [hb, _root_.mul_one], fun χ y J hJ => ?_⟩⟩
  · have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm
  · have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [hv χ y J hJ, hb, C.face₃]

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem qkAct_exists (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) {k : ℕ} (a : O) (p : QkPt D F k) :
    ∃ p', QkAct oa a p p' := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hr := oa.onB.rosati (star a)
  have hbal := oa.tau_bal (star a)
  rw [star_star] at hr hbal
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have ra := fun {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) =>
    ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ
  have vu : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ x w : TF (R := R) F ⟶ D.P.A,
      val (LB.pullGen D.P.L _ _ u (lift x w).left) (𝟙 _) y J = val₂ u y J x w := fun hJ x w => by
    rw [val_pull hJ, Category.id_comp]; rfl
  have u₁ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J 1 w = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).1
    rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have u₂ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J w 1 = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).2
    rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have ex : ∀ g : GtPtF D F, ∃ g' : GtPtF D F, g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
    intro g
    have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 _) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun χ y J hJ =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (vu hJ _ _))
    obtain ⟨g', hb, hv⟩ := exists_gt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left))
      (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu _)) (fun χ U _ h => by
        refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
          (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
        rw [prod_gt, cf]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (fun y J hJ => by
        rw [vv 0 y J hJ, smul_zero, cPoint_zero, u₁ hJ, _root_.mul_one]
        exact (val_corr hJ g.s_zero _).trans (val_one _)) (fun χ χ' y J hJ => by
        have e₁ := (ra hJ (cP D _ χ) (cP D _ χ') g.b).1
        have e₂ := gt_mul (𝟙 (TF (R := R) F)) hJ g (star a • χ) (star a • χ')
        rw [Category.id_comp, cf, cf, Over.id_left] at e₂
        rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, smul_add, cPoint_add, _root_.mul_assoc]
        refine (congrArg _ e₁).trans ?_
        rw [← _root_.mul_assoc]
        exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _))
    exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩
  choose act hb hv using ex
  have add : ∀ g g' g'' : GtPtF D F, g.IsAdd g' g'' → (act g).IsAdd (act g') (act g'') := fun g g' g'' h => by
    obtain ⟨b₁, v₁⟩ := (isAdd_iff _ _ _).1 h
    refine (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, b₁, MonObj.mul_comp], fun χ y J hJ => ?_⟩
    have e₁ := (ra hJ g.b g'.b (cP D _ χ)).2
    have e₂ := v₁ (star a • χ) y J hJ
    rw [cf] at e₂
    rw [← b₁] at e₁
    rw [hv _ _ y J hJ, hv _ _ y J hJ, hv _ _ y J hJ, hb, hb, _root_.mul_assoc]
    refine (congrArg _ e₁).trans ?_
    rw [← _root_.mul_assoc]
    exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _)
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p.eq
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  let q : QkPt D F k := ⟨a • p.y, act p.g, act h, ⟨fun i => act (gs i), by
      obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 g₀
      exact (isZero_iff _).2 ⟨by rw [hb, z₁, MonObj.one_comp], fun χ y J hJ => by
        rw [hv _ _ y J hJ, z₂ _ y J hJ, z₁, u₂ hJ, _root_.mul_one]⟩,
      fun i => add _ _ _ (gst i), congrArg act gl⟩, (isIota_iff _ _).2 ⟨by rw [hb, ιb, cf], fun χ y J hJ => by
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by
        rw [Category.id_comp]; rfl)
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ χ p.y) κ.left)
      have e' : val (LB.pullGen D.P.L _ _ u (D.pt2 χ p.y)) κ.left y J = val₂ u y J (cP D _ χ) (cP D _ p.y) := by
        rw [val_pull hJ, val₂, ← comp_cP D κ, ← comp_cP D κ p.y, ← comp_lift]; rfl
      rw [hv _ _ y J hJ, ιv _ y J hJ, ιb, ← e']
      exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
        (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))⟩⟩
  refine ⟨q, q, rfl, ⟨hb _, fun u' hu' u₀' χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩, qk_equiv_refl hB q⟩
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (hv p.g χ y J hJ).symm)
  rw [val_pull hJ, Category.id_comp]
  have z2 : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  exact gen_unique D.P.isLB _ (zero2 D.P.A) z2 (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) hu' hu
    (fun y I hI => by
      have a₁ := val_corr hI u₀' (𝟙 _)
      have a₂ := val_corr hI u₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a₁ a₂
      exact a₁.trans a₂.symm) _ _ y J hJ

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
