import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLA
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

noncomputable section

namespace GlobalTheory.ShellMass

theorem shell_mass : ∀ (n : ℕ), 1 ≤ n → ∀ (p : V n) (O : Set (V n)) (Z : V n → V n) (lam : V n → ℝ), IsOpen O → p ∈ O → DifferentiableOn ℂ Z O → Z p = 0 → (fderiv ℂ Z p).det ≠ 0 → ContinuousOn lam O → ∀ (φ : V n → ℝ) (l τ : ℝ), ContinuousOn φ O → 0 < l → 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ball p ρ ⊆ O ∧ ∀ b : ℝ, ∫⁻ v in ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b}, ENNReal.ofReal (Real.exp (-φ v) * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) ≤ ENNReal.ofReal ((1 + τ) * (Real.pi ^ n / ((n - 1).factorial : ℝ) * (l / n)) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) := by
  classical
  intro n hn p O Z lam hO hpO hZ hZp hdet hlam φ l τ hφ hl hτ
  have hZc : ContDiffOn ℂ ∞ Z O := by
    refine contDiffOn_piLp' (p := 2) fun i => ?_
    have hd : DifferentiableOn ℂ (fun x => Z x i) O :=
      (EuclideanSpace.proj i : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hZ
    have ha : AnalyticOnNhd ℂ (fun x => Z x i) O := fun z hz =>
      ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hO hd hz
    exact ha.contDiffOn hO.uniqueDiffOn
  have hZa : ContDiffAt ℂ ∞ Z p := hZc.contDiffAt (hO.mem_nhds hpO)
  set E0 := (fderiv ℂ Z p).toContinuousLinearEquivOfDetNeZero hdet
  have hs : HasStrictFDerivAt Z (E0 : V n →L[ℂ] V n) p := by
    simpa [E0] using hZa.hasStrictFDerivAt (by norm_cast)
  set e := hs.toOpenPartialHomeomorph Z
  have he : (e : V n → V n) = Z := rfl
  have hpe : p ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  have hdetc : ContinuousOn (fun v => (fderiv ℂ Z v).det) O :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hZc.continuousOn_fderiv_of_isOpen hO (by norm_cast))
  set D : V n → ℝ := fun v => ‖(fderiv ℂ Z v).det‖ ^ 2 with hD
  have hDc : ContinuousAt D p := ((hdetc.continuousAt (hO.mem_nhds hpO)).norm).pow 2
  have hD0 : 0 < D p := pow_pos (norm_pos_iff.2 hdet) 2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set c := l / n with hcdef
  have hc : 0 < c := div_pos hl hnr
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ Real.exp (2 * η) * (c + 2 * η) < (1 + τ) * c := by
    refine Filter.Eventually.and eventually_mem_nhdsWithin (nhdsWithin_le_nhds ?_)
    have ht : Tendsto (fun η : ℝ => Real.exp (2 * η) * (c + 2 * η)) (𝓝 0)
        (𝓝 (Real.exp (2 * 0) * (c + 2 * 0))) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (continuous_const.add (continuous_const.mul continuous_id))).tendsto 0
    simp only [mul_zero, Real.exp_zero, one_mul, add_zero] at ht
    exact ht.eventually (gt_mem_nhds (by nlinarith))
  obtain ⟨η, hη, hηc⟩ := hev.exists
  have hlamc : ContinuousAt lam p := hlam.continuousAt (hO.mem_nhds hpO)
  have hgc : ContinuousAt (fun v => -φ v + (n : ℝ) * lam v) p :=
    ((hφ.continuousAt (hO.mem_nhds hpO)).neg).add (continuousAt_const.mul hlamc)
  have h1 : ∀ᶠ v in 𝓝 p, v ∈ O := hO.mem_nhds hpO
  have h2 : ∀ᶠ v in 𝓝 p, v ∈ e.source := e.open_source.mem_nhds hpe
  have h3 : ∀ᶠ v in 𝓝 p, lam v ∈ ball (lam p) η := hlamc.eventually (ball_mem_nhds _ hη)
  have h4 : ∀ᶠ v in 𝓝 p, (-φ v + (n : ℝ) * lam v) ∈ ball (-φ p + (n : ℝ) * lam p) η :=
    hgc.eventually (ball_mem_nhds _ hη)
  have h5 : ∀ᶠ v in 𝓝 p, D p * Real.exp (-η) < D v := by
    refine hDc.eventually (lt_mem_nhds ?_)
    have : Real.exp (-η) < 1 := (Real.exp_lt_exp.2 (by linarith : -η < 0)).trans_eq Real.exp_zero
    nlinarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and (h3.and (h4.and h5))))
  have hbO : ball p ρ ⊆ O := fun v hv => (hball v hv).1
  have hinj : Set.InjOn Z (ball p ρ) := by
    rw [← he]; exact e.injOn.mono fun v hv => (hball v hv).2.1
  refine ⟨ρ, hρ, hbO, ?_⟩
  intro b
  set a1 := Real.exp ((b - l) / n + lam p - η) with ha1
  set a2 := Real.exp (b / n + lam p + η) with ha2
  have ha1p : 0 < a1 := Real.exp_pos _
  have h21 : a2 / a1 = Real.exp (c + 2 * η) := by
    rw [ha1, ha2, ← Real.exp_sub, hcdef]; congr 1; ring
  have ha12 : a1 ≤ a2 := by
    rw [ha1, ha2]; refine Real.exp_le_exp.2 ?_
    have : (b - l) / n ≤ b / n := div_le_div_of_nonneg_right (by linarith) hnr.le
    linarith
  set Ann := {w : V n | a1 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ a2} with hAnn
  have hAnnm : MeasurableSet Ann :=
    ((isClosed_le continuous_const (continuous_norm.pow 2)).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)).measurableSet
  set K := Real.exp (2 * η) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hfm' : Measurable fun w : V n => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ))) :=
    ((measurable_norm.pow_const 2).pow_const _).ennreal_ofReal
  set f : V n → ℝ≥0∞ := fun w => ENNReal.ofReal K *
      Ann.indicator (fun w => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ)))) w with hfdef
  have hfm : Measurable f := measurable_const.mul (hfm'.indicator hAnnm)
  set Zb : V n → V n := (ball p ρ).piecewise Z (fun _ => 0) with hZb
  have hZbm : Measurable Zb :=
    ContinuousOn.measurable_piecewise (hZ.continuousOn.mono hbO) continuousOn_const measurableSet_ball
  set G : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (D v) * f (Zb v) with hG
  have hGm : Measurable G := by
    refine Measurable.mul ?_ (hfm.comp hZbm)
    refine Measurable.ennreal_ofReal ?_
    exact ((ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℂ Z)).norm).pow_const 2

  have hpt : ∀ v ∈ ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧
      ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b},
      ENNReal.ofReal (Real.exp (-φ v) * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) ≤ G v := by
    rintro v ⟨hvb, hv0, hvl, hvu⟩
    obtain ⟨-, -, hv3, hv4, hv5⟩ := hball v hvb
    rw [mem_ball, Real.dist_eq, abs_lt] at hv3 hv4
    set s := ‖Z v‖ ^ 2 with hsdef
    have hsp : 0 < s := pow_pos (norm_pos_iff.2 hv0) 2
    have hlog : Real.log (s * Real.exp (-lam v)) = Real.log s - lam v := by
      rw [Real.log_mul hsp.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    rw [hlog] at hvl hvu ⊢
    have hl1 : (b - l) / n ≤ Real.log s - lam v := by rw [div_le_iff₀ hnr]; linarith
    have hl2 : Real.log s - lam v ≤ b / n := by rw [le_div_iff₀ hnr]; linarith
    have hA : Z v ∈ Ann := by
      refine ⟨?_, ?_⟩
      · exact (Real.exp_le_exp.2 (by linarith)).trans_eq (Real.exp_log hsp)
      · exact (Real.exp_log hsp).symm.trans_le (Real.exp_le_exp.2 (by linarith))
    have hZbv : Zb v = Z v := Set.piecewise_eq_of_mem _ _ _ hvb
    simp only [hG, hfdef, hZbv, Set.indicator_of_mem hA]
    rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsn : s ^ (-(n : ℝ)) = Real.exp (-(n : ℝ) * Real.log s) := by
      rw [Real.rpow_def_of_pos hsp]; ring_nf
    have heq : Real.exp (-φ v) * Real.exp (-((n : ℝ) * (Real.log s - lam v))) =
        Real.exp (-φ v + (n : ℝ) * lam v) * s ^ (-(n : ℝ)) := by
      rw [hsn, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [heq]
    have hexp : Real.exp (-φ v + (n : ℝ) * lam v) ≤ D v * K := by
      have e1 : Real.exp (-φ v + (n : ℝ) * lam v) ≤ Real.exp (-φ p + n * lam p + η) :=
        Real.exp_le_exp.2 (by linarith)
      have e2 : Real.exp (-φ p + n * lam p + η) = D p * Real.exp (-η) * K := by
        rw [hK, show ‖(fderiv ℂ Z p).det‖ ^ 2 = D p from rfl, div_eq_mul_inv]
        have hDi : D p * (D p)⁻¹ = 1 := mul_inv_cancel₀ hD0.ne'
        have hx : Real.exp (-φ p + n * lam p + η) =
            Real.exp (-η) * Real.exp (2 * η) * Real.exp (-φ p + n * lam p) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [hx]
        linear_combination (-(Real.exp (-η) * Real.exp (2 * η) * Real.exp (-φ p + n * lam p))) * hDi
      rw [e2] at e1
      exact e1.trans (mul_le_mul_of_nonneg_right hv5.le hK0)
    have hsn0 : 0 ≤ s ^ (-(n : ℝ)) := Real.rpow_nonneg hsp.le _
    calc Real.exp (-φ v + (n : ℝ) * lam v) * s ^ (-(n : ℝ)) ≤ D v * K * s ^ (-(n : ℝ)) :=
          mul_le_mul_of_nonneg_right hexp hsn0
      _ = D v * (K * s ^ (-(n : ℝ))) := by ring
  have hcov := ReciprocityTheory.L2DbarEstimates.I.cov n (ball p ρ) Z f isOpen_ball (hZ.mono hbO) hinj hfm
  have hpol := ReciprocityTheory.L2DbarEstimates.I.polar n hn a1 a2 ha1p ha12
  calc _ ≤ ∫⁻ v in ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧
        ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b}, G v := setLIntegral_mono hGm hpt
    _ ≤ ∫⁻ v in ball p ρ, G v := lintegral_mono_set Set.inter_subset_left
    _ = ∫⁻ w in Z '' ball p ρ, f w := by
        rw [hcov]
        refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
        simp only [hG, hD, Set.piecewise_eq_of_mem _ _ _ hv, hZb]
    _ ≤ ∫⁻ w, f w := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal K * ENNReal.ofReal (Real.pi ^ n / ((n - 1).factorial : ℝ) * Real.log (a2 / a1)) := by
        rw [hfdef, lintegral_const_mul _ (hfm'.indicator hAnnm), lintegral_indicator hAnnm, hpol]
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul hK0]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [h21, Real.log_exp, hK]
        have hP : 0 ≤ Real.pi ^ n / ((n - 1).factorial : ℝ) := by positivity
        have hE : 0 ≤ Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2 := by positivity
        calc Real.exp (2 * η) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2) *
              (Real.pi ^ n / ((n - 1).factorial : ℝ) * (c + 2 * η))
            = (Real.pi ^ n / ((n - 1).factorial : ℝ) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) *
              (Real.exp (2 * η) * (c + 2 * η)) := by ring
          _ ≤ (Real.pi ^ n / ((n - 1).factorial : ℝ) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) *
              ((1 + τ) * c) := mul_le_mul_of_nonneg_left hηc.le (mul_nonneg hP hE)
          _ = _ := by rw [hcdef]; ring

end GlobalTheory.ShellMass
