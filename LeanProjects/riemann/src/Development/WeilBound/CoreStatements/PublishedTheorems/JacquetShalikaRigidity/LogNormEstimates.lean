import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LogNormEstimates

theorem log_le {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (h1 : a ≤ D) (h2 : D ≤ b) :
    |Real.log D| ≤ |Real.log a| + |Real.log b| := by
  have l1 := Real.log_le_log ha h1
  have l2 := Real.log_le_log hD h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

theorem norm_le {p : ℂ} {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (h : p ≠ 0 → a ≤ D ∧ D ≤ b) (z z₀ : ℂ) :
    ‖p * (D : ℂ) ^ z‖ ≤ ‖p * (D : ℂ) ^ z₀‖ * Real.exp ((|Real.log a| + |Real.log b|) * |z.re - z₀.re|) := by
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨h1, h2⟩ := h hp
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  have e : D ^ z.re = D ^ z₀.re * D ^ (z.re - z₀.re) := by
    rw [← Real.rpow_add hD]; congr 1; ring
  rw [e, ← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos hD]
  apply Real.exp_le_exp.2
  calc Real.log D * (z.re - z₀.re) ≤ |Real.log D * (z.re - z₀.re)| := le_abs_self _
    _ = |Real.log D| * |z.re - z₀.re| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (log_le hD ha h1 h2) (abs_nonneg _)

theorem re_eq (p : ℂ) {D : ℝ} (hD : 0 < D) (σ u : ℝ) :
    (p * (D : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re = D ^ σ * (p * (D : ℂ) ^ ((u : ℂ) * Complex.I)).re := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hD.ne'), ← Complex.ofReal_cpow hD.le σ,
    show p * (((D ^ σ : ℝ) : ℂ) * (D : ℂ) ^ ((u : ℂ) * Complex.I)) =
      ((D ^ σ : ℝ) : ℂ) * (p * (D : ℂ) ^ ((u : ℂ) * Complex.I)) by ring, Complex.re_ofReal_mul]

set_option synthInstance.maxHeartbeats 400000 in
theorem msc {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} :
    MeasurableSingletonClass (GA E k) := inferInstance

end LogNormEstimates

theorem log_norm_estimate_of_Q : Q1 → D0 → N3 → C0 → D1 := by
  intro hQ1 hD0 hN3 hC0
  unfold D1 ForMu
  intro E _ _ _ k μ _ hk β hβ S P u z₀ hPc hPinv hP1 hpos hint
  obtain ⟨hDpos, hDmul, hDc, -, hDUU, -⟩ := hD0 E k
  obtain ⟨hG0o, h1G0, hG0inv, -⟩ := hC0 E k S
  obtain ⟨hNP, -, -, hN0⟩ := hN3 E k
  obtain ⟨hνs, hνinv, -⟩ := hNP 0 (by omega)
  obtain ⟨a, b, ha, hab⟩ := hpos
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hDmul 1 1
    simp only [mul_one] at h
    exact (mul_left_cancel₀ (hDpos 1).ne' (by rw [mul_one]; exact h.symm))
  have hG0m : MeasurableSet (G0 (k := k) S) := hG0o.measurableSet
  have hcont : ∀ z : ℂ, Continuous fun g : GA E k => P g * (Dt g : ℂ) ^ z := fun z =>
    hPc.mul ((Complex.continuous_ofReal.comp hDc).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g))
  set L := |Real.log a| + |Real.log b| with hL
  have hL0 : 0 ≤ L := by positivity
  have hdom : ∀ g ∈ G0 (k := k) S, ∀ z : ℂ,
      ‖P g * (Dt g : ℂ) ^ z‖ ≤ ‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * |z.re - z₀.re|) := by
    intro g hg z
    exact LogNormEstimates.norm_le (hDpos g) ha (fun hp => ⟨(hab g hg hp).1, (hab g hg hp).2.1⟩) z z₀
  have hintG : ∀ z : ℂ, Integrable (fun g => P g * (Dt g : ℂ) ^ z) ((μ.withDensity β).restrict (G0 S)) := by
    intro z
    refine Integrable.mono' ((hint.norm.mul_const (Real.exp (L * |z.re - z₀.re|))).restrict)
      (hcont z).aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem hG0m fun g hg => hdom g hg z
  refine ⟨fun z₁ => ?_, fun σ => ?_⟩
  · have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (μ.withDensity β).restrict (G0 S))
      (F := fun z g => P g * (Dt g : ℂ) ^ z)
      (F' := fun z g => P g * (Dt g : ℂ) ^ z * ((Real.log (Dt g) : ℝ) : ℂ)) (x₀ := z₁)
      (bound := fun g => ‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * (|z₁.re - z₀.re| + 1)) * L) (Metric.ball_mem_nhds z₁ zero_lt_one)
      (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable) (hintG z₁)
      ((hcont z₁).mul (Complex.continuous_ofReal.comp (hDc.log fun g => (hDpos g).ne'))).aestronglyMeasurable
      ?_ (((hint.norm.mul_const _).mul_const _).restrict) ?_
    · exact hderiv.2.differentiableAt
    · refine ae_restrict_of_forall_mem hG0m fun g hg z hz => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hp : P g = 0
      · simp only [hp, zero_mul, norm_zero]; positivity
      have hlog := LogNormEstimates.log_le (hDpos g) ha (hab g hg hp).1 (hab g hg hp).2.1
      have hz' : |z.re - z₀.re| ≤ |z₁.re - z₀.re| + 1 := by
        have h1 : |z.re - z₁.re| ≤ 1 := by
          have := Complex.abs_re_le_norm (z - z₁)
          rw [Metric.mem_ball, dist_eq_norm] at hz
          rw [Complex.sub_re] at this; linarith
        calc |z.re - z₀.re| = |(z.re - z₁.re) + (z₁.re - z₀.re)| := by ring_nf
          _ ≤ |z.re - z₁.re| + |z₁.re - z₀.re| := abs_add_le _ _
          _ ≤ _ := by linarith
      have e1 := hdom g hg z
      have e2 : Real.exp (L * |z.re - z₀.re|) ≤ Real.exp (L * (|z₁.re - z₀.re| + 1)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz' hL0)
      calc ‖P g * (Dt g : ℂ) ^ z‖ * |Real.log (Dt g)|
          ≤ (‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * (|z₁.re - z₀.re| + 1))) * L := by
            apply mul_le_mul _ hlog (abs_nonneg _) (by positivity)
            exact e1.trans (mul_le_mul_of_nonneg_left e2 (norm_nonneg _))
        _ = _ := rfl
    · refine Filter.Eventually.of_forall fun g z _ => ?_
      have hD := hDpos g
      have h := ((hasDerivAt_id z).const_cpow (c := (Dt g : ℂ))
        (Or.inl (Complex.ofReal_ne_zero.2 hD.ne'))).const_mul (P g)
      have e : P g * ((Dt g : ℂ) ^ id z * Complex.log (Dt g) * 1) =
          P g * (Dt g : ℂ) ^ z * ((Real.log (Dt g) : ℝ) : ℂ) := by
        rw [Complex.ofReal_log hD.le]; simp only [id, mul_one]; ring
      exact h.congr_deriv e
  · set f : GA E k → ℝ := fun g => (P g * (Dt g : ℂ) ^ ((u : ℂ) * Complex.I)).re with hf
    have hfc : Continuous f := Complex.continuous_re.comp (hcont _)
    set O : Set (GA E k) := G0 S ∩ {g | 0 < f g} with hO
    have hOo : IsOpen O := hG0o.inter (isOpen_lt continuous_const hfc)
    have hOm : MeasurableSet O := hOo.measurableSet
    have h1O : (1 : GA E k) ∈ O := by
      refine ⟨h1G0, ?_⟩
      show 0 < (P 1 * ((Dt (1 : GA E k) : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I)).re
      rw [hD1, Complex.ofReal_one, Complex.one_cpow, mul_one]; exact hP1
    have hOinv : ∀ n g, UU 0 n → (n * g ∈ O ↔ g ∈ O) := by
      intro n g hn
      simp only [hO, hf, Set.mem_inter_iff, Set.mem_setOf_eq, hG0inv n g hn, hPinv n hn g, hDmul, hDUU 0 n hn,
        one_mul]
    haveI : MeasurableSingletonClass (GA E k) := LogNormEstimates.msc
    have hμO : μ O ≠ 0 := (hOo.measure_pos μ ⟨1, h1O⟩).ne'
    have hβO : μ.withDensity β O ≠ 0 := by
      intro h0
      apply hμO
      have hin : ∀ g, ∫⁻ r, O.indicator 1 (r * g) ∂nuP E k 0 = O.indicator 1 g * nuP E k 0 Set.univ := by
        intro g
        rw [← lintegral_const]
        apply lintegral_congr_ae
        filter_upwards [(hN0 hk).1] with r hr
        by_cases hg : g ∈ O
        · simp [Set.indicator_apply, hg, (hOinv r g hr).2 hg]
        · simp [Set.indicator_apply, hg, mt (hOinv r g hr).1 hg]
      have key := hQ1 (GA E k) μ (Measure.dirac 1) (nuP E k 0) {1} (fun _ => 1) β
        (by rw [Measure.map_dirac' measurable_inv, inv_one]) (by rw [ae_dirac_eq]; exact rfl)
        ⟨measurable_const, fun g => by simp⟩ hβ.1
        (fun g => by
          simp only [lintegral_dirac, mul_one]
          calc ∫⁻ r, β (r⁻¹ * g) ∂nuP E k 0 = ∫⁻ r, β (r * g) ∂(Measure.map (fun h => h⁻¹) (nuP E k 0)) :=
                (lintegral_map (hβ.1.comp (measurable_mul_const g)) measurable_inv).symm
            _ = 1 := by rw [hνinv]; exact hβ.2 g)
        (O.indicator 1) (measurable_one.indicator hOm) (by rintro h rfl g; simp)
      have hw : μ.withDensity (fun _ => (1 : ℝ≥0∞)) = μ := withDensity_one
      rw [hw, lintegral_indicator_one hOm] at key
      rw [key]
      simp_rw [hin]
      rw [lintegral_mul_const _ (measurable_one.indicator hOm), lintegral_indicator_one hOm, h0, zero_mul]
    intro hzero
    have hFi := hintG ((σ : ℂ) + u * Complex.I)
    have hre := integral_re hFi
    rw [hzero] at hre
    simp only [RCLike.re_to_complex, Complex.zero_re] at hre
    have hpos' := (setIntegral_pos_iff_support_of_nonneg_ae (s := G0 S) (μ := μ.withDensity β)
      (f := fun g => (P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re)
      (ae_restrict_of_forall_mem hG0m fun g hg => ?_) hFi.re).2 ?_
    · linarith
    · by_cases hp : P g = 0
      · simp [hp]
      show 0 ≤ (P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re
      rw [LogNormEstimates.re_eq _ (hDpos g)]
      exact mul_nonneg (Real.rpow_nonneg (hDpos g).le _) (hab g hg hp).2.2
    · refine lt_of_lt_of_le (pos_iff_ne_zero.2 hβO) (measure_mono fun g hg => ⟨?_, hg.1⟩)
      rw [Function.mem_support, LogNormEstimates.re_eq _ (hDpos g)]
      exact (mul_pos (Real.rpow_pos_of_pos (hDpos g) σ) hg.2).ne'

end PositivityTheory.AdelicQuotientData

end
