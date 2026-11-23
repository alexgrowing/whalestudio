import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftTraces

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftOrigin

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem gt_rel (oa : D.toPre.OAct O) (a : O) (g g' h g0 : GtPtF D.toPre F) (z : D.toPre.X)
    (hgt : GtAct oa a g g') (hι : GtPtF.IsIota z h) (hadd : g'.IsAdd h g0) (hz : g0.IsZero)
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L)) :
    g.b ≫ oa.onB.act a = cP D.toPre _ (-z) ∧
      ∀ (χ : D.toPre.X) (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J →
        val (g.s (star a • χ)) (𝟙 _) y J * val r (lift (DegPre.cF D.toPre F χ) g.b).left y J =
          val (D.toPre.tau (-z) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J := by
  obtain ⟨hb', hs'⟩ := hgt
  rw [isIota_iff] at hι
  obtain ⟨hbh, hsh⟩ := hι
  rw [isAdd_iff] at hadd
  obtain ⟨hb0, hs0⟩ := hadd
  rw [isZero_iff] at hz
  obtain ⟨hz0, hzs⟩ := hz
  have hneg : cP D.toPre (TF (R := V) F) z * cP D.toPre (TF (R := V) F) (-z) = 1 := by
    rw [← cPoint_add, add_neg_cancel, cPoint_zero]
  have h1 : g'.b * h.b = 1 := by rw [← hb0, hz0]
  have hgb : g'.b = cP D.toPre (TF (R := V) F) (-z) := by
    calc g'.b = g'.b * (cP D.toPre (TF (R := V) F) z * cP D.toPre (TF (R := V) F) (-z)) := by
          rw [hneg, _root_.mul_one]
      _ = (g'.b * h.b) * cP D.toPre (TF (R := V) F) (-z) := by rw [hbh, _root_.mul_assoc]
      _ = cP D.toPre (TF (R := V) F) (-z) := by rw [h1, _root_.one_mul]
  refine ⟨hb'.symm.trans hgb, ?_⟩
  intro χ y J hJ
  have e1 : val (g.s (star a • χ)) (𝟙 _) y J * val r (lift (DegPre.cF D.toPre F χ) g.b).left y J =
      val (g'.s χ) (𝟙 _) y J := by
    rw [← val_corr (h := hs' r hr hr0 χ) (r := 𝟙 _), val_mul, val_pull, Category.id_comp]
    all_goals first | exact hJ | rfl
  rw [e1]
  have e2 := hs0 χ y J hJ
  rw [hzs χ y J hJ, _root_.one_mul, hsh χ y J hJ] at e2
  have e4 : th D.toPre y J (cP D.toPre _ χ) g'.b h.b =
      th D.toPre y J (cP D.toPre (TF (R := V) F) χ) (cP D.toPre (TF (R := V) F) (-z))
        (cP D.toPre (TF (R := V) F) z) := by
    rw [hgb, hbh]
  rw [e4] at e2
  have hc3 : IsCub (th D.toPre y J) := isCub_cubV _ hJ
  have e5 : val (D.toPre.tau (-z + z) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J *
        th D.toPre y J (cP D.toPre (TF (R := V) F) (-z)) (cP D.toPre (TF (R := V) F) z)
          (cP D.toPre (TF (R := V) F) χ) =
      val (D.toPre.tau (-z) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J *
        val (D.toPre.tau z χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J :=
    tau_mul (σ := 𝟙 (TF (R := V) F)) (hJ := hJ) D.tau_bimult (-z) z χ
  have e6 : val (D.toPre.tau (0 + 0) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J *
        th D.toPre y J (cP D.toPre (TF (R := V) F) 0) (cP D.toPre (TF (R := V) F) 0)
          (cP D.toPre (TF (R := V) F) χ) =
      val (D.toPre.tau 0 χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J *
        val (D.toPre.tau 0 χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J :=
    tau_mul (σ := 𝟙 (TF (R := V) F)) (hJ := hJ) D.tau_bimult 0 0 χ
  rw [cPoint_zero, hc3.face, _root_.mul_one, add_zero] at e6
  have t0 : val (D.toPre.tau 0 χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J = 1 :=
    mul_left_cancel (e6.symm.trans (_root_.mul_one _).symm)
  rw [neg_add_cancel, t0, _root_.one_mul] at e5
  rw [hc3.s01, hc3.s12, e5] at e2
  exact (mul_right_cancel e2).symm

private theorem mul_mul_mul_mul_inv_eq_mul_mul_mul {G : Type*} [CommGroup G] (u rr gs r0 ps rk : G) :
    u * rr * (gs * (r0 * (ps * rk) * u⁻¹)) = r0 * (gs * rr * (ps * rk)) := by
  calc u * rr * (gs * (r0 * (ps * rk) * u⁻¹)) = (u * u⁻¹) * (r0 * (gs * rr * (ps * rk))) := by ac_rfl
    _ = r0 * (gs * rr * (ps * rk)) := by rw [_root_.mul_inv_cancel, _root_.one_mul]

theorem origin (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (N : ℕ) (p : QkPt D.toPre F (1 * N))
    (z : D.toPre.X)
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (hrel : ∀ (χ : D.toPre.X) (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J →
        val (p.g.s (star a • χ)) (𝟙 _) y J * val r (lift (DegPre.cF D.toPre F χ) p.g.b).left y J =
          val (D.toPre.tau (-z) χ) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J)
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε 1 N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F)))
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε (1 * N)))) (hw : w.IsGen)
    (hwv : ∀ (y : (TF (R := V) F).left) J, Good D.toPre.P.L y J → val w (𝟙 (TF (R := V) F).left) y J =
        val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F))
            (𝟙 (TF (R := V) F).left) y J *
          val (LB.pullGen D.toPre.P.L _ _ (LB.mulGen D.toPre.P.L _ _ _ _
            (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1))
              (jFK (R := V) F)) (𝟙 (TF (R := V) F).left) y J *
          (val u0 (DegPre.zF D.toPre F ≫ DegPre.trPt D.toPre F p.g.b).left y J)⁻¹)
    (χ : D.toPre.X)
    (uχ : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε 1 N))) (huχ : uχ.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F)))
    (uχz : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a (χ - z)) (pullε 1 N)))
    (hcz : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχz (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (1 * (N - 1))) (jFK (R := V) F)))
    (fe : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.deltaφ D.toPre F 1 χ (-z)) (DegPre.deltaε 1)))
    (hcfe : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ fe (DegPre.zF D.toPre F).left)
      (DegPre.famMult D.toPre F 1 (-z) χ))
    (Φ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.phiφ D.toPre F p.y (star a • χ) p.g.b) (DegPre.deltaε (1 * N))))
    (hΦ : Φ.IsGen)
    (hcΦ : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ Φ (DegPre.zF D.toPre F).left)
      (LB.mulGen D.toPre.P.L _ _ _ _ (p.g.s (star a • χ)) w))
    (y : (TF (R := V) F).left) (J) (hJ : Good D.toPre.P.L y J) :
    val (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uχ (DegPre.trPt D.toPre F p.g.b).left) Φ)
        (DegPre.zF D.toPre F).left y J =
      val (LB.mulGen D.toPre.P.L _ _ _ _ uχz (LB.pullGen D.toPre.P.L _ _ fe (aF D F oa a).left))
        (DegPre.zF D.toPre F).left y J := by
  have C : IsCub (th D.toPre (T := TF (R := V) F) y J) := isCub_cubV D.toPre.cub hJ
  have z1 : DegPre.zF D.toPre F ≫ fst (TF (R := V) F) D.toPre.P.A = 𝟙 _ := lift_fst _ _
  have z2 : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have hu1 : uVal D.toPre F (1 * N) (star a • χ) p.g.b (DegPre.zF D.toPre F) y J = 1 := by
    unfold uVal
    rw [z2, C.N_one, C.face₂, inv_one, _root_.mul_one]
  have hl : ((DegPre.zF D.toPre F).left ≫ (DegPre.trPt D.toPre F p.g.b).left) ≫
      (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left = (lift (DegPre.cF D.toPre F χ) p.g.b).left := by
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_cP, CanonicalLiftTraces.zF_tr_pr]
    rfl
  have e1 := val_corr hJ hcz (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at e1
  have e2 := val_corr hJ hcfe (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at e2
  have e3 := val_famMult (𝟙 (TF (R := V) F)) hJ 1 (-z) χ
  simp only [Over.id_left] at e3
  have e4 : val (LB.pullGen D.toPre.P.L _ _ (LB.mulGen D.toPre.P.L _ _ _ _
      (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1))
        (jFK (R := V) F)) (𝟙 (TF (R := V) F).left) y J =
      val (GeneratorPullback.powGen D.toPre.P.L _ _ (D.toPre.psi (-z)) 1) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J *
        val (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK 1) (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y J := by
    rw [val_pull hJ, val_mul hJ]
  have e5 := hwv y J hJ
  rw [e4, Over.comp_left] at e5
  have e6 := hrel χ y J hJ
  have e7 : val fe ((DegPre.zF D.toPre F).left ≫ (aF D F oa a).left) y J = val fe (DegPre.zF D.toPre F).left y J := by
    rw [← Over.comp_left, CanonicalLiftTraces.zF_aF]
  have hΦv : val Φ (DegPre.zF D.toPre F).left y J = val (LB.mulGen D.toPre.P.L _ _ _ _ (p.g.s (star a • χ)) w)
      (DegPre.zF D.toPre F ≫ fst (TF (R := V) F) D.toPre.P.A).left y J := by
    rw [(gen_phi hG p w hw (star a • χ)).2 Φ hΦ hcΦ _ (DegPre.zF D.toPre F) y J hJ, hu1]
    exact one_mul _
  rw [val_mul hJ, val_pull hJ, val_mul hJ, val_pull hJ,
    hΦv,
    CanonicalLiftValuation.pull_val_chi hG oa a 1 N χ uχ huχ hc u0 hu0 hc0 r hr hr0 _ _ y J hJ, val_pull hJ, hl, z1,
    Over.id_left, val_mul hJ, e5, e7, e1, e2, e3, ← e6]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftOrigin
