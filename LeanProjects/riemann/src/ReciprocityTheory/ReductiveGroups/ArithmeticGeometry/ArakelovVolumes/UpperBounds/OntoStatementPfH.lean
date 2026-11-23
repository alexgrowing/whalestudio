import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH

open NumberField Complex Matrix Topology Filter MeasureTheory Set Metric ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoC ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoF ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

private theorem continuous_dmin_apply (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.dmin ReciprocityTheory.ChartRestriction.G.FD.lminor ReciprocityTheory.ChartRestriction.G.FD.gram
    ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col ReciprocityTheory.ChartRestriction.G.FD.mat
  refine Continuous.matrix_det ?_
  refine Continuous.matrix_submatrix ?_ _ _
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => ?_
  refine Continuous.mul (Continuous.mul ?_ continuous_const) ?_
  · exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply τ))
  · exact Complex.continuous_conj.comp
      ((continuous_apply _).comp ((continuous_apply _).comp (continuous_apply τ)))

private theorem isOpen_data_dom : IsOpen X.dom := by
  show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re}
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => ?_
  refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · refine isOpen_ne_fun (Continuous.matrix_det ?_) continuous_const
    unfold ReciprocityTheory.ChartRestriction.G.FD.mat
    exact continuous_apply τ
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp (continuous_dmin_apply X τ i)))

private theorem cpt_continuous : Continuous fun z => cpt X x0 z := by
  unfold cpt rmul nmat mat
  refine continuous_pi fun τ => ?_
  refine Continuous.matrix_mul continuous_const ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · first
      | fun_prop
      | exact (EuclideanSpace.proj _).continuous
  · exact continuous_const
  · exact continuous_const

private theorem measurableSet_omF : MeasurableSet (OmF X x0) :=
  ((isOpen_data_dom X).preimage (cpt_continuous X x0)).measurableSet

theorem muF_ac : muF X x0 ≪ volume.restrict (OmF X x0) := by
  unfold muF
  exact withDensity_absolutelyContinuous _ _

theorem aem_of {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {f : V (nd X) → β} (hf : ContinuousOn f (OmF X x0)) : AEMeasurable f (muF X x0) :=
  (hf.aemeasurable (measurableSet_omF X x0)).mono_ac (muF_ac X x0)

theorem ae_mem_Om : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 :=
  (muF_ac X x0).ae_le (ae_restrict_mem (measurableSet_omF X x0))

theorem ae_mem_nonvanishingLocus {g1 : V (nd X) → ℂ} (hg1 : DifferentiableOn ℂ g1 (OmF X x0))
    (hC : IsPreconnected (OmF X x0)) (hne : ∃ z ∈ OmF X x0, g1 z ≠ 0) :
    ∀ᵐ z ∂muF X x0, z ∈ Om1 X x0 g1 := by
  have h0 : volume.restrict (OmF X x0) (Om1 X x0 g1)ᶜ = 0 := by
    rw [Measure.restrict_apply (isOpen_nonvanishingLocus X x0 hg1).measurableSet.compl]
    refine measure_mono_null ?_ (null_zero (isOpen_OmF X x0) hC hg1 hne)
    intro z hz
    refine ⟨hz.2, ?_⟩
    by_contra h
    exact hz.1 ⟨hz.2, h⟩
  rw [Filter.eventually_iff, mem_ae_iff]
  exact muF_ac X x0 h0

theorem measW {W : Frame X.Ψ r → ℝ≥0∞} (hW : Measurable W) : Measurable fun z => W (cpt X x0 z) :=
  hW.comp (cpt_continuous X x0).measurable

theorem vanish (hExG : ExhaustGStatement (E := E)) (hGrad : RhGradFStatement (E := E))
    (hKa : KaUnfoldStatement (E := E)) (hPair : PairUnfoldStatement (E := E))
    (hBig : BigCellStatement (E := E)) (hConn : OmFConnStatement (E := E))
    (hExtF : ExtFStatement (E := E)) (hx0 : IsOrth X x0) (hPD : PropDisc X)
    {la : Wt X.Ψ r} {W : Frame X.Ψ r → ℝ≥0∞} {Ps : Frame X.Ψ r → ℝ} {g1 : V (nd X) → ℂ} {bb m : ℝ}
    (hW : IsMetricW X la W) (hWL : WLower X la W) (hbb4 : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb)
    (hm : bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m)
    (hg1 : DifferentiableOn ℂ g1 (OmF X x0)) (hg1ne : ∃ z ∈ OmF X x0, g1 z ≠ 0)
    (hPs : ContDiffOn ℝ ∞ (fun z => Ps (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0})
    (hWPs : ∀ z, z ∈ OmF X x0 → g1 z ≠ 0 →
      W (cpt X x0 z) = ENNReal.ofReal (Real.exp (-Ps (cpt X x0 z))))
    (hLev : ∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → ∀ ξ : Fin (nd X) → ℂ,
      m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
        (leviV (nd X) (fun w => ((Ps (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re)
    {FF : Set (V (nd X))} (hFF : IsFundSet X x0 FF) {f0 : Frame X.Ψ r → ℂ} (hf0 : f0 ∈ X.SS la)
    (hf0F : InFF X x0 W FF f0)
    (horth : ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) →
      InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) →
      ∫ z in FF, poin X la P (cpt X x0 z) * conj (f0 (cpt X x0 z)) *
        ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 = 0) :
    ∀ x ∈ X.dom, f0 x = 0 := by
  have hO := isOpen_OmF X x0
  have hC' := hConn r X x0 hx0
  have hbb : 0 < bb := lt_of_le_of_lt (by positivity) hbb4
  have hsec : X.IsSec la f0 := hf0.1.1
  have hgd : DifferentiableOn ℂ (fun z => f0 (cpt X x0 z)) (OmF X x0) := hol_comp X x0 hsec.1
  have hgc := hgd.continuousOn
  obtain ⟨c, hc, hWL'⟩ := hWL
  have hWm := measW X x0 hW.1
  obtain ⟨C, hCt, hC⟩ := hKa r X x0 hx0 hPD FF hFF bb hbb4
  have hφ := hC (phiF X f0 W) (phiF_meas X hsec.1.continuousOn hW.1) (phiF_B X hsec.2.1 hW)
    (phiF_G X hsec.2.2 hW)
  set I := ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z * ‖f0 (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0
    with hIdef
  have hIeq : I = ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * phiF X f0 W (cpt X x0 z) ∂muF X x0 := by
    refine lintegral_congr_ae ((ae_mem_Om X x0).mono fun z hz => ?_)
    dsimp only
    rw [phiF_dom X f0 W hz, ENNReal.ofReal_mul (show 0 ≤ kaF X x0 bb z from (Real.exp_pos _).le),
      mul_assoc]
  have hFFeq : ∫⁻ z in FF, phiF X f0 W (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in FF, ENNReal.ofReal (‖f0 (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0 :=
    setLIntegral_congr_fun hFF.1 (fun z hz => phiF_dom X f0 W (hFF.2.1 hz))
  have hIt : I < ⊤ := by
    rw [hIeq]
    refine hφ.trans_lt (ENNReal.mul_lt_top hCt ?_)
    rw [hFFeq]
    exact hf0F
  obtain ⟨F', hF', hJ⟩ := horm_step X x0 hExG hGrad hx0 hbb hm hg1 hPs hWPs hLev hsec.1
  set q : ℝ := bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) / (m - bb) with hqdef
  have hC0 : (0 : ℝ) ≤ ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmb : 0 < m - bb := by nlinarith [mul_nonneg (sq_nonneg bb) hC0]
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg (sq_nonneg _) hC0) hmb.le
  have hq1 : q < 1 := (div_lt_one hmb).2 (by linarith)
  have hae1 := ae_mem_nonvanishingLocus X x0 hg1 hC' hg1ne
  have hres : (muF X x0).restrict (Om1 X x0 g1) = muF X x0 := Measure.restrict_eq_self_of_ae_mem hae1
  rw [hres] at hJ
  set J := ∫⁻ z, ENNReal.ofReal (‖(kaF X x0 bb z : ℂ) * f0 (cpt X x0 z) - F' z‖ ^ 2 /
    kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 with hJdef
  have hJt : J < ⊤ := hJ.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIt)
  have hka : ∀ z, 0 < kaF X x0 bb z := fun z => Real.exp_pos _
  have hkac : ContinuousOn (kaF X x0 bb) (OmF X x0) := fun z hz =>
    (ka_contDiffAt bb hz).continuousAt.continuousWithinAt
  have hF0c : ContinuousOn (fun z => (kaF X x0 bb z : ℂ) * f0 (cpt X x0 z)) (OmF X x0) :=
    (Complex.continuous_ofReal.comp_continuousOn hkac).mul hgc
  have hJt' : ∫⁻ z in Om1 X x0 g1, ENNReal.ofReal (‖(kaF X x0 bb z : ℂ) * f0 (cpt X x0 z) - F' z‖ ^ 2 /
      kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 < ⊤ := by rw [hres]; exact hJt
  have hL2 := localRepresentationL2 X x0 hc hWL' hg1 hF0c hJt'
  obtain ⟨F, hFd, hFeq⟩ := ext_glue hO hC' hg1 hg1ne hF' hL2
  have hFF' : ∀ z ∈ Om1 X x0 g1, F z = F' z := fun z hz => hFeq z hz.1 hz.2
  have hFc := hFd.continuousOn
  have hInAt : InAt X x0 W bb F := by
    unfold InAt
    have hpt : ∀ᵐ z ∂muF X x0, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ≤
        2 * (ENNReal.ofReal (kaF X x0 bb z * ‖f0 (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z)) +
        2 * (ENNReal.ofReal (‖(kaF X x0 bb z : ℂ) * f0 (cpt X x0 z) - F' z‖ ^ 2 / kaF X x0 bb z) *
          W (cpt X x0 z)) := by
      refine hae1.mono fun z hz => ?_
      rw [hFF' z hz]
      have hk := hka z
      have h1 := sq_sub_le ((kaF X x0 bb z : ℂ) * f0 (cpt X x0 z)) (F' z)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, mul_pow] at h1
      have h2 : ‖F' z‖ ^ 2 / kaF X x0 bb z ≤ 2 * (kaF X x0 bb z * ‖f0 (cpt X x0 z)‖ ^ 2) +
          2 * (‖(kaF X x0 bb z : ℂ) * f0 (cpt X x0 z) - F' z‖ ^ 2 / kaF X x0 bb z) := by
        rw [div_le_iff₀ hk]
        have e : (2 * (kaF X x0 bb z * ‖f0 (cpt X x0 z)‖ ^ 2) +
            2 * (‖(kaF X x0 bb z : ℂ) * f0 (cpt X x0 z) - F' z‖ ^ 2 / kaF X x0 bb z)) * kaF X x0 bb z =
            2 * (kaF X x0 bb z ^ 2 * ‖f0 (cpt X x0 z)‖ ^ 2) +
            2 * ‖(kaF X x0 bb z : ℂ) * f0 (cpt X x0 z) - F' z‖ ^ 2 := by field_simp
        rw [e]; exact h1
      calc ENNReal.ofReal (‖F' z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)
          ≤ ENNReal.ofReal (2 * (kaF X x0 bb z * ‖f0 (cpt X x0 z)‖ ^ 2) +
              2 * (‖(kaF X x0 bb z : ℂ) * f0 (cpt X x0 z) - F' z‖ ^ 2 / kaF X x0 bb z)) *
              W (cpt X x0 z) := by gcongr
        _ = _ := by
            rw [ENNReal.ofReal_add (mul_nonneg zero_le_two (mul_nonneg (hka z).le (sq_nonneg _)))
              (mul_nonneg zero_le_two (div_nonneg (sq_nonneg _) (hka z).le)),
              ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_mul (p := 2) (by norm_num),
              ENNReal.ofReal_ofNat]
            ring
    refine (lintegral_mono_ae hpt).trans_lt ?_
    rw [lintegral_add_left' ?_, lintegral_const_mul' _ _ (by simp),
      lintegral_const_mul' _ _ (by simp)]
    · exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hIt, ENNReal.mul_lt_top (by simp) hJt⟩
    · exact ((ENNReal.measurable_ofReal.comp_aemeasurable (aem_of X x0
        (hkac.mul (hgc.norm.pow 2)))).mul hWm.aemeasurable).const_mul 2
  have hka1 : ∀ z ∈ OmF X x0, kaF X x0 bb z ≤ 1 := fun z hz => by
    unfold kaF
    rw [Real.exp_le_one_iff]
    have := ExF.rhF_nonneg X x0 hx0 hz
    nlinarith
  obtain ⟨P, hP, hPF⟩ := hExtF r X x0 hx0 la F hFd (fun Cs _ _ => by
    have hpt : ∀ᵐ z ∂muF X x0, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ≤
        ENNReal.ofReal (1 / c) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := by
      refine (ae_mem_Om X x0).mono fun z hz => ?_
      have hk := hka z
      have e : ‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z)) =
          1 / c * (‖F z‖ ^ 2 * (c * Real.exp (-phla X la (cpt X x0 z)))) := by field_simp
      rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      gcongr
      · exact le_div_self (by positivity) hk (hka1 z hz)
      · exact hWL' _ hz
    calc ∫⁻ z in sat X x0 Cs, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0
        ≤ ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 :=
          setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ z, ENNReal.ofReal (1 / c) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) *
            W (cpt X x0 z)) ∂muF X x0 := lintegral_mono_ae hpt
      _ < ⊤ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hInAt)
  have h1 := horth F P hFd hInAt hP hPF
  have h2 := hPair r X x0 hx0 hPD la W bb hW ⟨c, hc, hWL'⟩ hbb4 F P hFd hInAt hP hPF FF hFF f0 hf0 hf0F
  rw [h1] at h2
  have hI0 : I = 0 := by
    refine I_zero (μ := muF X x0) (k := kaF X x0 bb) (g := fun z => f0 (cpt X x0 z))
      (u := fun z => (kaF X x0 bb z : ℂ) * f0 (cpt X x0 z) - F z) (w := fun z => W (cpt X x0 z))
      (Filter.Eventually.of_forall hka) ?_ hq1 hq0 (aem_of X x0 hkac) (aem_of X x0 hgc)
      (aem_of X x0 (hF0c.sub hFc)) hWm.aemeasurable hIt ?_ ?_
    · refine hae1.mono fun z hz => ?_
      rw [hWPs z hz.1 hz.2]; exact ENNReal.ofReal_lt_top
    · refine le_trans (le_of_eq ?_) hJ
      refine lintegral_congr_ae (hae1.mono fun z hz => ?_)
      simp only [hFF' z hz]
    · rw [h2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [sub_sub_cancel]
  have hg0 : ∀ z ∈ OmF X x0, f0 (cpt X x0 z) = 0 := by
    have hae : ∀ᵐ z ∂muF X x0,
        ENNReal.ofReal (kaF X x0 bb z * ‖f0 (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) = 0 :=
      (lintegral_eq_zero_iff' ((ENNReal.measurable_ofReal.comp_aemeasurable (aem_of X x0
        (hkac.mul (hgc.norm.pow 2)))).mul hWm.aemeasurable)).1 hI0
    have hae' : ∀ᵐ z ∂muF X x0, f0 (cpt X x0 z) = 0 := by
      refine (hae.and (ae_mem_Om X x0)).mono fun z hz => ?_
      obtain ⟨h, hzΩ⟩ := hz
      rcases mul_eq_zero.1 h with h | h
      · rw [ENNReal.ofReal_eq_zero] at h
        have hk := hka z
        have : ‖f0 (cpt X x0 z)‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖f0 (cpt X x0 z)‖]
        exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1
          (le_antisymm this (sq_nonneg _)))
      · exfalso
        have h3 := hWL' _ hzΩ
        rw [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h3
        have := mul_pos hc (Real.exp_pos (-phla X la (cpt X x0 z)))
        linarith
    have haev : ∀ᵐ z ∂volume.restrict (OmF X x0), f0 (cpt X x0 z) = 0 := by
      unfold muF at hae'
      rw [ae_withDensity_iff (measurable_densF X x0)] at hae'
      filter_upwards [hae', ae_restrict_mem hO.measurableSet] with z h hz
      exact h (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact densF_pos hz)
    intro z hz
    by_contra hne
    have hev : ∀ᶠ y in 𝓝 z, y ∈ OmF X x0 ∧ f0 (cpt X x0 y) ≠ 0 :=
      (hO.eventually_mem hz).and ((hgc.continuousAt (hO.mem_nhds hz)).eventually_ne hne)
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
    have h0 := ae_iff.1 haev
    have hpos : 0 < volume.restrict (OmF X x0) (ball z ρ) := by
      rw [Measure.restrict_apply measurableSet_ball,
        Set.inter_eq_left.2 fun y hy => (hball y hy).1]
      exact measure_ball_pos _ _ hρ
    exact hpos.ne' (measure_mono_null (fun y hy => (hball y hy).2) h0)
  exact hBig r X x0 hx0 la f0 ⟨hsec.1, hsec.2.1⟩ hg0

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
