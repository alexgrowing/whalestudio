import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem hy (n : ℕ) (Y : Type u) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] (hH : HAll.{u} n) (hE : EXTStatement n) (hN : EXTNullStatement n) :
    HYStatement n Y ι La := by
  intro A L la N w w0 s De σ ps F0 h hD hF hσ hps hPos hF0 hh hdb
  classical
  by_cases hfin : ∫⁻ y, h y * ENNReal.ofReal (Real.exp (-ps y)) ∂A.mu = ⊤
  · refine ⟨fun _ _ => 0, ⟨fun i => differentiableOn_const 0, fun i j y _ _ _ => by simp⟩, ?_⟩
    rw [hfin]; exact le_top
  set M := A.Mset w0 s De with hMdef
  set X := flatStein A hD hF with hX
  have hMo : IsOpen M := isOpen_Mset A hD
  set Φ := hyPhi A w0 s σ la ps with hΦdef
  set u0 := sectionFrameQuotient A F0 σ with hu0def
  set nσ := A.nsq (A.kap + la) σ with hnσdef
  have hpsc : Continuous ps := hyq_smoothFn_cont A hps
  have hΦs : SmoothR n X.z (fun y : M => Φ y) := smoothR_flat A hD hF Φ (fun x hx =>
    ⟨A.pick x, A.mem_pick x, hyq_phi_smooth A hD hF hσ hps hx _ (A.mem_pick x)⟩)
  have hΦl : LeviNonneg n X.z (fun y : M => Φ y) := leviNonneg_flat A hD hF Φ (fun x hx =>
    ⟨A.pick x, A.mem_pick x, hyq_phi_smooth A hD hF hσ hps hx _ (A.mem_pick x), fun ξ => by
      rw [hyq_levi_phi A hD hF hσ hps hx _ (A.mem_pick x)]
      exact hPos _ _ (A.mem_pick x) ξ⟩)
  have hu0s : Smooth n X.z (fun y : M => u0 y) := smooth_flat A hD hF u0 (fun x hx =>
    ⟨A.pick x, A.mem_pick x, contDiffAt_sectionFrameQuotient A hD hσ hF0 hx _ (A.mem_pick x)⟩)
  have hnσs : SmoothR n X.z (fun y : M => nσ y) := smoothR_flat A hD hF nσ (fun x hx =>
    ⟨A.pick x, A.mem_pick x, hyq_nsig_smooth A hD hσ hx _ (A.mem_pick x)⟩)
  have hnσc : Continuous (fun y : M => nσ y) := by
    have := Complex.continuous_re.comp (Smooth.continuous n X.z X.isLocalHomeomorph _ hnσs)
    exact this
  have hu0c : Continuous (fun y : M => u0 y) := Smooth.continuous n X.z X.isLocalHomeomorph _ hu0s

  set hHf : M → ℝ≥0∞ := fun x => h x * ENNReal.ofReal (nσ x)⁻¹ with hHfdef
  have hHm : Measurable hHf :=
    (hh.comp measurable_subtype_coe).mul (ENNReal.measurable_ofReal.comp hnσc.measurable.inv)
  have hdbM : ∀ (x : M) (η : Fin n → ℂ), ENNReal.ofReal (‖dbarDot n X.z (fun y : M => u0 y) x η‖ ^ 2) ≤
      hHf x * ENNReal.ofReal (Levi n X.z (fun y : M => Φ y) x η).re := by
    intro x η
    have hi := A.mem_pick (x : Y)
    have hdet := jz_det_ne A hD hF x x.2 (A.pick x) hi
    set J' := (jz A w0 s (A.pick x) x).toContinuousLinearEquivOfDetNeZero hdet
    set ξ : Fin n → ℂ := WithLp.ofLp (J'.symm (WithLp.toLp 2 η)) with hξ
    have hη : (fun k => jz A w0 s (A.pick x) x (WithLp.toLp 2 ξ) k) = η := by
      have h1 : jz A w0 s (A.pick x) x (WithLp.toLp 2 ξ) = WithLp.toLp 2 η := by
        have h2 := ((jz A w0 s (A.pick x) x).toContinuousLinearEquivOfDetNeZero hdet).apply_symm_apply
          (WithLp.toLp 2 η)
        rw [ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply] at h2
        simpa [J', ξ] using h2
      rw [h1]
    rw [← hη, ← dbar_flat_loc A hD hF u0 (A.pick x) x hi (contDiffAt_sectionFrameQuotient A hD hσ hF0 x.2 _ hi) ξ,
      ← levi_flat_loc A hD hF Φ (A.pick x) x hi (hyq_phi_smooth A hD hF hσ hps x.2 _ hi) ξ,
      hyq_levi_phi A hD hF hσ hps x.2 _ hi, dbar_sectionFrameQuotient A hD hσ hF0 x.2 _ hi]
    have key := hdb (A.pick x) x hi ξ
    have hσne := hyq_sigma_ne A hσ x.2 (A.pick x) hi
    have e1 : ‖A.dbarAt (A.pick x) F0 x ξ / σ (A.pick x) x‖ ^ 2 =
        (‖A.dbarAt (A.pick x) F0 x ξ‖ ^ 2 * Real.exp (-A.ph (A.kap + la) (A.pick x) x)) * (nσ x)⁻¹ := by
      simp only [hnσdef, nsq]
      rw [norm_div, div_pow, mul_inv, Real.exp_neg, inv_inv]
      field_simp
    rw [e1, ENNReal.ofReal_mul (by positivity)]
    calc _ ≤ h x * ENNReal.ofReal (A.leviAt (A.pick x) (fun y => A.ph la (A.pick x) y + ps y) x ξ) *
          ENNReal.ofReal (nσ x)⁻¹ := by gcongr
      _ = _ := by simp only [hHfdef]; ring
  obtain ⟨Fu, hFu, hFbd⟩ := hH M X (fun y => Φ y) (fun y => u0 y) hHf hΦs hΦl hu0s hHm hdbM

  set ut : Y → ℂ := fun y => if hy : y ∈ M then Fu ⟨y, hy⟩ else 0 with hutdef
  have hut : (fun y : M => ut y) = Fu := funext fun y => dif_pos y.2
  have hutc : Continuous (fun y : M => ut y) := by
    rw [hut]; exact Smooth.continuous n X.z X.isLocalHomeomorph _ (Holo.smooth n X.z _ hFu)
  set Fs : ι → Y → ℂ := fun i y => σ i y * ut y with hFsdef
  have hFs : A.IsSecOn (A.kap + la) M Fs := by
    refine ⟨fun i => ?_, fun i j y hy hi hj => ?_⟩
    · have h1 := (holo_flat_iff A hD hF ut).1 (by rw [hut]; exact hFu) i
      exact (hσ.1.1 i).mul h1
    · simp only [hFsdef]; rw [hσ.1.2 i j y hy hi hj]; ring

  set ψ0 : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (nσ y * ‖u0 y - ut y‖ ^ 2 * Real.exp (-ps y))
    with hψ0def
  set ψ : Y → ℝ≥0∞ := M.indicator ψ0 with hψdef
  have hψm : Measurable ψ := by
    refine measurable_of_restrict_of_restrict_compl hMo.measurableSet ?_ ?_
    · have hc : Continuous (fun y : M => ψ0 y) :=
        ENNReal.continuous_ofReal.comp ((hnσc.mul ((hu0c.sub hutc).norm.pow 2)).mul
          (Real.continuous_exp.comp (hpsc.comp continuous_subtype_val).neg))
      have : M.domRestrict ψ = fun y : M => ψ0 y := funext fun y => by
        show M.indicator ψ0 y = ψ0 y; exact Set.indicator_of_mem y.2 _
      rw [this]; exact hc.measurable
    · have : Mᶜ.domRestrict ψ = fun _ => 0 := funext fun y => by
        show M.indicator ψ0 y = 0; exact Set.indicator_of_notMem y.2 _
      rw [this]; exact measurable_const
  have hae : ∀ᵐ y ∂A.mu, y ∈ M := by
    rw [ae_iff]; simpa [Set.compl_def] using mu_compl_Mset A hN hD hF
  have hre : ∀ f : Y → ℝ≥0∞, ∫⁻ y, f y ∂A.mu = ∫⁻ y in M, f y ∂A.mu := fun f => by
    rw [Measure.restrict_eq_self_of_ae_mem hae]
  set nJ := A.nsq A.kap (fun i y => (jz A w0 s i y).det) with hnJdef
  have hdens : ∀ x : M, Real.exp (A.ph A.kap (A.pick x) x) / ‖(jz A w0 s (A.pick x) x).det‖ ^ 2 =
      (nJ x)⁻¹ := by
    intro x
    have hJp := hyq_nJ_pos A hD hF x.2
    simp only [hnJdef, nsq] at hJp ⊢
    rw [Real.exp_neg, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  have hexp : ∀ x : M, Real.exp (-Φ x) = nσ x * Real.exp (-ps x) * (nJ x)⁻¹ := by
    intro x
    have hσp := hyq_nsig_pos A hσ x.2
    have hJp := hyq_nJ_pos A hD hF x.2
    have e : -Φ x = Real.log (nσ x) - Real.log (nJ x) + -ps x := by
      simp only [hΦdef, hyPhi, hnσdef, hnJdef]; ring
    rw [e, Real.exp_add, Real.exp_sub, Real.exp_log hσp, Real.exp_log hJp]; ring
  have hI1 : ∫⁻ y, ψ y ∂A.mu = wint n X.z (fun x => u0 x - Fu x) (fun y => Φ y) := by
    rw [hre, lintegral_flat A hD hF ψ hψm, wint]
    refine lintegral_congr fun x => ?_
    have hσp := hyq_nsig_pos A hσ x.2
    rw [hψdef, Set.indicator_of_mem x.2]
    show ENNReal.ofReal (nσ x * ‖u0 x - ut x‖ ^ 2 * Real.exp (-ps x)) * _ = _
    rw [show ut x = Fu x from congrFun hut x, ← ENNReal.ofReal_mul (by positivity), hdens x, hexp x]
    congr 1; ring
  have hI2 : ∫⁻ x, hHf x * ENNReal.ofReal (Real.exp (-(fun y : M => Φ y) x)) ∂vol n X.z =
      ∫⁻ y in M, h y * ENNReal.ofReal (Real.exp (-ps y)) ∂A.mu := by
    rw [lintegral_flat A hD hF (fun y => h y * ENNReal.ofReal (Real.exp (-ps y))) (hh.mul
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hpsc.neg).measurable))]
    refine lintegral_congr fun x => ?_
    have hσp := hyq_nsig_pos A hσ x.2
    have hJp := hyq_nJ_pos A hD hF x.2
    rw [hHfdef, mul_assoc, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), hdens x]
    show h x * ENNReal.ofReal ((nσ x)⁻¹ * Real.exp (-Φ x)) = _
    rw [hexp x]
    congr 2
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (show nσ x ≠ 0 from hσp.ne'), one_mul]
  have hint : ∫⁻ y, ψ y ∂A.mu ≤ ∫⁻ y, h y * ENNReal.ofReal (Real.exp (-ps y)) ∂A.mu := by
    rw [hI1]
    exact hFbd.trans (hI2.le.trans (setLIntegral_le_lintegral _ _))
  have hψfin : ∫⁻ y, ψ y ∂A.mu < ⊤ := hint.trans_lt (lt_top_iff_ne_top.2 hfin)

  have hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ M, ENNReal.ofReal (A.nsq (A.kap + la) Fs x) ∂A.mu < ⊤ := by
    intro y0
    have hi := A.mem_pick y0
    set e := A.chart (A.pick y0) with he
    obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 e.open_target (e y0) (e.map_source hi)
    have hcb : closedBall (e y0) (r / 2) ⊆ e.target :=
      (closedBall_subset_ball (by linarith)).trans hrt
    have hS : ContinuousOn e.symm (closedBall (e y0) (r / 2)) := e.continuousOn_symm.mono hcb
    obtain ⟨C1, hC1⟩ := hyq_bdd (f := fun v => ‖F0 (A.pick y0) (e.symm v)‖ ^ 2 *
      Real.exp (-A.ph (A.kap + la) (A.pick y0) (e.symm v))) (c := e y0) (r := r / 2) (by
        have h1 := (hF0.1 (A.pick y0)).continuousOn.mono hcb
        have h2 := (A.smooth_ph (A.kap + la) (A.pick y0)).continuousOn.mono hcb
        exact (h1.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn h2.neg))
    obtain ⟨C2, hC2⟩ := hyq_bdd (f := fun v => ps (e.symm v)) (c := e y0) (r := r / 2)
      (hpsc.comp_continuousOn hS)
    obtain ⟨C3, hC3⟩ := hyq_bdd (f := fun v => Real.exp (A.ph A.kap (A.pick y0) (e.symm v)))
      (c := e y0) (r := r / 2) (Real.continuous_exp.comp_continuousOn
        ((A.smooth_ph A.kap (A.pick y0)).continuousOn.mono hcb))
    set U := e.source ∩ e ⁻¹' ball (e y0) (r / 2) with hU
    have hUo : IsOpen U := e.isOpen_inter_preimage isOpen_ball
    have hyU : y0 ∈ U := ⟨hi, mem_ball_self (by linarith)⟩
    have hUM : MeasurableSet (U ∩ M) := (hUo.inter hMo).measurableSet
    refine ⟨U, hUo.mem_nhds hyU, ?_⟩
    have hC1n : 0 ≤ C1 := le_trans (by positivity) (hC1 (e y0) (mem_closedBall_self (by linarith)))
    have hpt : ∀ x ∈ U ∩ M, ENNReal.ofReal (A.nsq (A.kap + la) Fs x) ≤
        ENNReal.ofReal (2 * C1) + ENNReal.ofReal (2 * Real.exp C2) * ψ x := by
      rintro x ⟨⟨hxs, hxb⟩, hxM⟩
      have hv : e x ∈ closedBall (e y0) (r / 2) := ball_subset_closedBall hxb
      have hSx : e.symm (e x) = x := e.left_inv hxs
      have h1 := hC1 _ hv
      have h2 := hC2 _ hv
      simp only [hSx] at h1 h2
      have hF0x : A.nsq (A.kap + la) F0 x =
          ‖F0 (A.pick y0) x‖ ^ 2 * Real.exp (-A.ph (A.kap + la) (A.pick y0) x) :=
        hyq_nsq_chart A _ F0 _ x hxs (hF0.2 _ _ x hxs (A.mem_pick x))
      have hσne := hyq_sigma_ne A hσ hxM (A.pick x) (A.mem_pick x)
      have hFsx : A.nsq (A.kap + la) Fs x = nσ x * ‖ut x‖ ^ 2 := by
        simp only [nsq, hFsdef, hnσdef, norm_mul, mul_pow]; ring
      have hF0x' : A.nsq (A.kap + la) F0 x = nσ x * ‖u0 x‖ ^ 2 := by
        simp only [nsq, hnσdef, hu0def, sectionFrameQuotient, norm_div, div_pow]; field_simp
      have hσp := hyq_nsig_pos A hσ hxM
      set t := nσ x * ‖u0 x - ut x‖ ^ 2 * Real.exp (-ps x) with ht
      have hψx : ψ x = ENNReal.ofReal t := by rw [hψdef, Set.indicator_of_mem hxM]
      have ht0 : 0 ≤ t := by positivity
      have hpar : ‖ut x‖ ^ 2 ≤ 2 * ‖u0 x‖ ^ 2 + 2 * ‖u0 x - ut x‖ ^ 2 := by
        have h0 : ‖ut x‖ ≤ ‖u0 x‖ + ‖u0 x - ut x‖ := by
          calc ‖ut x‖ = ‖u0 x - (u0 x - ut x)‖ := by rw [sub_sub_cancel]
            _ ≤ _ := norm_sub_le _ _
        have h3 : ‖ut x‖ ^ 2 ≤ (‖u0 x‖ + ‖u0 x - ut x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
        nlinarith [sq_nonneg (‖u0 x‖ - ‖u0 x - ut x‖)]
      have hte : nσ x * ‖u0 x - ut x‖ ^ 2 = Real.exp (ps x) * t := by
        rw [ht, Real.exp_neg]; field_simp
      have hkey : A.nsq (A.kap + la) Fs x ≤ 2 * C1 + 2 * Real.exp C2 * t := by
        have he2 : Real.exp (ps x) ≤ Real.exp C2 := Real.exp_le_exp.2 h2
        calc A.nsq (A.kap + la) Fs x = nσ x * ‖ut x‖ ^ 2 := hFsx
          _ ≤ nσ x * (2 * ‖u0 x‖ ^ 2 + 2 * ‖u0 x - ut x‖ ^ 2) := by gcongr
          _ = 2 * A.nsq (A.kap + la) F0 x + 2 * (Real.exp (ps x) * t) := by rw [hF0x', ← hte]; ring
          _ ≤ 2 * C1 + 2 * (Real.exp C2 * t) := by
            rw [hF0x]; gcongr
          _ = 2 * C1 + 2 * Real.exp C2 * t := by ring
      rw [hψx, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      exact ENNReal.ofReal_le_ofReal hkey
    calc ∫⁻ x in U ∩ M, ENNReal.ofReal (A.nsq (A.kap + la) Fs x) ∂A.mu
        ≤ ∫⁻ x in U ∩ M, (ENNReal.ofReal (2 * C1) + ENNReal.ofReal (2 * Real.exp C2) * ψ x) ∂A.mu :=
          setLIntegral_mono' hUM hpt
      _ = ENNReal.ofReal (2 * C1) * A.mu (U ∩ M) +
          ENNReal.ofReal (2 * Real.exp C2) * ∫⁻ x in U ∩ M, ψ x ∂A.mu := by
          rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hψm,
            Measure.restrict_apply_univ]
      _ < ⊤ := by
          have hmu : A.mu (U ∩ M) < ⊤ := by
            calc A.mu (U ∩ M) ≤ A.mu U := measure_mono Set.inter_subset_left
              _ = ∫⁻ v in e '' U, ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y0) (e.symm v))) :=
                  A.mu_chart _ U hUo.measurableSet Set.inter_subset_left
              _ ≤ ∫⁻ v in closedBall (e y0) (r / 2),
                  ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y0) (e.symm v))) :=
                  lintegral_mono_set (by
                    rintro _ ⟨y, ⟨_, hyb⟩, rfl⟩; exact ball_subset_closedBall hyb)
              _ ≤ ∫⁻ v in closedBall (e y0) (r / 2), ENNReal.ofReal C3 :=
                  setLIntegral_mono' measurableSet_closedBall
                    (fun v hv => ENNReal.ofReal_le_ofReal (hC3 v hv))
              _ = ENNReal.ofReal C3 * volume (closedBall (e y0) (r / 2)) := setLIntegral_const _ _
              _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
          have hψU : ∫⁻ x in U ∩ M, ψ x ∂A.mu < ⊤ :=
            (setLIntegral_le_lintegral _ _).trans_lt hψfin
          exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmu,
            ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψU⟩

  obtain ⟨G, hG, hGeq⟩ := ext_Mset A hE hD hF (A.kap + la) Fs hFs hloc
  refine ⟨G, hG, ?_⟩
  calc ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) (F0 - G) y * Real.exp (-ps y)) ∂A.mu
      = ∫⁻ y, ψ y ∂A.mu := by
        refine lintegral_congr_ae (hae.mono fun y hy => ?_)
        rw [hψdef, Set.indicator_of_mem hy]
        show ENNReal.ofReal (A.nsq (A.kap + la) (F0 - G) y * Real.exp (-ps y)) = ψ0 y
        have hσne := hyq_sigma_ne A hσ hy (A.pick y) (A.mem_pick y)
        have hGy := hGeq (A.pick y) y hy (A.mem_pick y)
        have e : A.nsq (A.kap + la) (F0 - G) y = nσ y * ‖u0 y - ut y‖ ^ 2 := by
          simp only [nsq, Pi.sub_apply, hGy, hFsdef, hnσdef, hu0def, sectionFrameQuotient]
          rw [show F0 (A.pick y) y - σ (A.pick y) y * ut y =
            σ (A.pick y) y * (F0 (A.pick y) y / σ (A.pick y) y - ut y) by field_simp, norm_mul,
            mul_pow]
          ring
        rw [e]
    _ ≤ _ := hint

end

end ReciprocityTheory.L2DbarEstimates.Y
