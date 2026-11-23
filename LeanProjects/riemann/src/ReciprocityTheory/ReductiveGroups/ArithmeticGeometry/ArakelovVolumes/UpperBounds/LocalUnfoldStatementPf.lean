import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldPfC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

theorem densF_meas {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) : Measurable fun w => ENNReal.ofReal (densF X x w) := by
  have hm : ∀ (τ : X.Ψ) (i : Fin r), Measurable fun w => ‖dmin X.Gm (cpt X x w) τ i.castSucc‖ :=
    fun τ i => (OntoB.cd_dmin (X := X) (x0 := x) (τ := τ) (i := i.castSucc)).continuous.norm.measurable
  have hf : ∀ (τ : X.Ψ) (i : Fin r), Measurable fun w => ‖dmin X.Gm (cpt X x w) τ i.castSucc‖ ^ (-2 : ℤ) := by
    intro τ i
    simp only [zpow_neg, zpow_ofNat]
    exact ((hm τ i).pow_const 2).inv
  have hp : Measurable fun w => densF X x w := by
    unfold densF
    exact Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => hf τ i
  exact ENNReal.measurable_ofReal.comp hp

theorem localUnfoldB_of {E : Type} [Field E] [NumberField E] [IsCMField E] (hLU : LUStatement (E := E)) :
    LocalUnfoldBStatement (E := E) := by
  intro r X x0 ho hPD FF hFF x1 hx1
  classical
  obtain ⟨x1', ho', b1, hb1, rfl⟩ := ortho_holds r X x1 hx1
  obtain ⟨D⟩ := ExtFPf.luData_of hLU X x1' ho'
  have := KU.countable_Γ X
  have hM := measInv_holds (E := E)
  obtain ⟨ρ1, hρ1, hball1⟩ := exists_ball X b1 D ho' hb1
  obtain ⟨ρ2, hρ2, hball2⟩ := Metric.isOpen_iff.mp (ExF.isOpen_OmF X x1') 0 (IW.zero_mem_OmF X x1' ho')
  set ρ0 : ℝ := min ρ1 ρ2 / 2 with hρ0def
  have hρ0 : 0 < ρ0 := by positivity
  have hρ01 : ρ0 < ρ1 := by have := min_le_left ρ1 ρ2; linarith
  have hρ02 : ρ0 < ρ2 := by have := min_le_right ρ1 ρ2; linarith
  have hcl : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D := fun z hz =>
    hball1 z (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hρ01))
  have hclO : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ OmF X x1' := fun z hz =>
    hball2 (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hρ02))
  obtain ⟨Kj, hKj⟩ := jac_bound X b1 D hcl
  obtain ⟨Kd, hKd⟩ := dens_bound X b1 D hcl
  refine ⟨ρ0, hρ0, fun ρ hρ hρle => ?_⟩
  have hbcl : Metric.ball (0 : V (nd X)) ρ ⊆ Metric.closedBall 0 ρ0 := fun z hz =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball hρle hz)
  have hbU : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D := hbcl.trans hcl
  have hbO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1' := hbcl.trans hclO
  have hopen := isOpen_sat D ho' hb1 hbO
  refine ⟨hopen, ENNReal.ofReal (max Kd 0 * max Kj 0), ENNReal.ofReal_lt_top, fun G hG hGB hGΓ => ?_⟩
  set x1 := rmul x1' b1 with hx1def
  set T := Tset X x1 ρ with hTdef
  have hT : MeasurableSet T := meas_Tset X b1 D ho' hbU hx1
  have hTeq : T = KU.Sset X x1' (Φ X b1 D '' Metric.ball 0 ρ) := Tset_eq X b1 D hbU
  have hTB : ∀ y b, b ∈ Bor X.Ψ r → (rmul y b ∈ T ↔ y ∈ T) := fun y b hb => by
    rw [hTeq]; exact KU.rmul_mem_S X hb
  have hS : MeasurableSet (KU.Sset X x0 FF) := KU.meas_S X ho hFF.1
  have hcpt0 := (KU.cont_cpt X x0).measurable
  have hcpt1 := (KU.cont_cpt X x1').measurable
  have hae0 : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := ExtFPf.ae_OmF (X := X) (x0 := x0)
  set Sat : Set (V (nd X)) := {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
    cpt X x0 z = lact γ (rmul (cpt X x1 z') b)} with hSatdef
  have hSat : MeasurableSet Sat := (hopen.preimage (KU.cont_cpt X x0)).measurableSet

  let H : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ y =>
    (KU.Sset X x0 FF).indicator 1 y * T.indicator 1 (lact γ.1⁻¹ y) * G y
  have hHm : ∀ γ, Measurable (H γ) := fun γ =>
    ((measurable_one.indicator hS).mul ((measurable_one.indicator hT).comp (KU.cont_lact X γ.1⁻¹).measurable)).mul hG
  have hHB : ∀ γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, H γ (rmul x b) = H γ x := by
    intro γ x hx b hb
    have e1 : rmul x b ∈ KU.Sset X x0 FF ↔ x ∈ KU.Sset X x0 FF := KU.rmul_mem_S X hb
    have e2 : lact γ.1⁻¹ (rmul x b) ∈ T ↔ lact γ.1⁻¹ x ∈ T := by rw [KU.lact_rmul']; exact hTB _ _ hb
    simp only [H, Set.indicator_apply, e1, e2, hGB x hx b hb, Pi.one_apply]

  have stepA : ∫⁻ z in FF ∩ Sat, G (cpt X x0 z) ∂muF X x0 ≤ ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 := by
    refine le_trans (setLIntegral_mono' (hFF.1.inter hSat) fun z hz => ?_) (setLIntegral_le_lintegral _ _)
    obtain ⟨hzF, γ, hγ, b, hb, z', hz', he⟩ := hz
    have hT1 : lact γ⁻¹ (cpt X x0 z) ∈ T := by
      rw [he, KU.lact_lact, inv_mul_cancel, KU.lact_one]
      exact ⟨⟨z', b⟩, ⟨hz', hb⟩, rfl⟩
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ, hγ⟩ : X.Γ))
    simp only [H, Set.indicator_of_mem ((KU.cpt_mem_S X ho z).mpr hzF), Set.indicator_of_mem hT1,
      Pi.one_apply, one_mul]
  have stepB : ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 = ∑' γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 :=
    lintegral_tsum fun γ => ((hHm γ).comp hcpt0).aemeasurable
  have stepC : ∀ γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 = ∫⁻ z, (KU.Sset X x0 FF).indicator 1
      (lact γ.1 (cpt X x0 z)) * (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) ∂muF X x0 := by
    intro γ
    rw [hM r X x0 (lact γ.1 x0) ho (KU.isOrth_lact X γ.2 ho) (H γ) (hHm γ) (hHB γ), KU.muF_lact X γ.2]
    refine lintegral_congr_ae (hae0.mono fun z hz => ?_)
    show H γ (cpt X (lact γ.1 x0) z) = _
    rw [KU.cpt_lact]
    simp only [H, KU.lact_lact, inv_mul_cancel, KU.lact_one, hGΓ γ.1 γ.2 _ hz]
    ring
  have hIm : ∀ γ : X.Γ, Measurable fun z => (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
      (lact γ.1 (cpt X x0 z)) * (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) := fun γ =>
    ((measurable_one.indicator hS).comp ((KU.cont_lact X γ.1).comp (KU.cont_cpt X x0)).measurable).mul
      (((measurable_one.indicator hT).comp hcpt0).mul (hG.comp hcpt0))
  have stepD : ∑' γ : X.Γ, ∫⁻ z, (KU.Sset X x0 FF).indicator 1 (lact γ.1 (cpt X x0 z)) *
      (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) ∂muF X x0 ≤
      ∫⁻ z, T.indicator 1 (cpt X x0 z) * G (cpt X x0 z) ∂muF X x0 := by
    rw [← lintegral_tsum fun γ => (hIm γ).aemeasurable]
    refine lintegral_mono fun z => ?_
    rw [ENNReal.tsum_mul_right]
    calc (∑' γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 (cpt X x0 z))) *
          (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z))
        ≤ 1 * (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) := by
          gcongr; exact FSM.atMostOnce X ho hFF _
      _ = _ := one_mul _
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, (fun y => T.indicator (1 : Frame X.Ψ r → ℝ≥0∞) y * G y) (rmul x b) =
      (fun y => T.indicator 1 y * G y) x := by
    intro x hx b hb
    simp only [Set.indicator_apply, hTB x b hb, hGB x hx b hb, Pi.one_apply]
  have stepE : ∫⁻ z, T.indicator 1 (cpt X x0 z) * G (cpt X x0 z) ∂muF X x0 =
      ∫⁻ w, T.indicator 1 (cpt X x1' w) * G (cpt X x1' w) ∂muF X x1' :=
    hM r X x0 x1' ho ho' (fun y => T.indicator 1 y * G y) ((measurable_one.indicator hT).mul hG) hφB
  have hA : MeasurableSet (Φ X b1 D '' Metric.ball 0 ρ) := meas_image X b1 D hbU hx1
  have stepF : ∫⁻ w, T.indicator 1 (cpt X x1' w) * G (cpt X x1' w) ∂muF X x1' =
      ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, G (cpt X x1' w) ∂muF X x1' := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun w => ?_
    have e : cpt X x1' w ∈ T ↔ w ∈ Φ X b1 D '' Metric.ball 0 ρ := by rw [hTeq]; exact KU.cpt_mem_S X ho' w
    by_cases hw : w ∈ Φ X b1 D '' Metric.ball 0 ρ
    · rw [Set.indicator_of_mem (e.mpr hw), Set.indicator_of_mem hw, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem (fun h => hw (e.mp h)), Set.indicator_of_notMem hw, zero_mul]
  have stepG : ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, G (cpt X x1' w) ∂muF X x1' ≤
      ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, ENNReal.ofReal (densF X x1' w) * G (cpt X x1' w) := by
    unfold muF
    rw [restrict_withDensity hA]
    refine (lintegral_withDensity_le_lintegral_mul _ (densF_meas X x1') _).trans ?_
    refine lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) (fun w => le_rfl)
  have hder : ∀ z ∈ Metric.ball (0 : V (nd X)) ρ,
      HasFDerivWithinAt (Φ X b1 D) (fderiv ℝ (Φ X b1 D) z) (Metric.ball 0 ρ) z := fun z hz =>
    ((((Φ_diffOn X b1 D) z (hbU hz)).differentiableAt ((isOpen_Uc X b1 D).mem_nhds (hbU hz))).restrictScalars ℝ
      ).hasFDerivAt.hasFDerivWithinAt
  have stepH : ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, ENNReal.ofReal (densF X x1' w) * G (cpt X x1' w) =
      ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal |(fderiv ℝ (Φ X b1 D) z).det| *
        (ENNReal.ofReal (densF X x1' (Φ X b1 D z)) * G (cpt X x1' (Φ X b1 D z))) :=
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hder
      ((Φ_injOn X b1 D hx1).mono hbU) _
  have stepI : ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal |(fderiv ℝ (Φ X b1 D) z).det| *
        (ENNReal.ofReal (densF X x1' (Φ X b1 D z)) * G (cpt X x1' (Φ X b1 D z))) ≤
      ENNReal.ofReal (max Kd 0 * max Kj 0) * ∫⁻ z in Metric.ball 0 ρ, G (cpt X x1 z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    obtain ⟨hΦO, hβ, e⟩ := split X b1 D (hbU hz)
    have hG1 : G (cpt X x1' (Φ X b1 D z)) = G (cpt X x1 z) := by
      rw [e, hGB _ (by exact hΦO) _ hβ]
    rw [hG1, ← mul_assoc]
    gcongr
    rw [ENNReal.ofReal_mul (le_max_right _ _), mul_comm]
    gcongr
    · exact (hKd z (hbcl hz)).trans (le_max_left _ _)
    · exact (hKj z (hbcl hz)).trans (le_max_left _ _)
  calc ∫⁻ z in FF ∩ Sat, G (cpt X x0 z) ∂muF X x0
      ≤ _ := stepA
    _ = _ := stepB
    _ = _ := tsum_congr stepC
    _ ≤ _ := stepD
    _ = _ := stepE
    _ = _ := stepF
    _ ≤ _ := stepG
    _ = _ := stepH
    _ ≤ _ := stepI

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem localUnfoldB_of {E : Type} [Field E] [NumberField E] [IsCMField E] (hLU : LUStatement (E := E)) :
    LocalUnfoldBStatement (E := E) := LUB.localUnfoldB_of hLU

end ReciprocityTheory.ChartRestriction.G.AR.Up
