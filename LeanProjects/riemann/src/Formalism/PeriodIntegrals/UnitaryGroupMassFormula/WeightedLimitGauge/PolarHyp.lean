import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace PI.RhsWLim.W.PH

theorem lintegral_fun_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ‖x‖ ∂μ = μ.toSphere univ *
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (Module.finrank ℝ E - 1)) * F y := by
  calc ∫⁻ x, F ‖x‖ ∂μ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), F ‖x.1‖ ∂(μ.comap (↑)) := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl (fun x => F ‖x‖),
          restrict_compl_singleton]
    _ = ∫⁻ p, F (p.2 : ℝ) ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
        rw [← (μ.measurePreserving_homeomorphUnitSphereProd).lintegral_comp_emb
          (Homeomorph.measurableEmbedding _)]
        simp
    _ = μ.toSphere univ * ∫⁻ y : Ioi (0 : ℝ), F y ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
        rw [lintegral_prod (fun p : (Metric.sphere (0 : E) 1) × Ioi (0 : ℝ) => F (p.2 : ℝ))
          (hF.comp (measurable_subtype_coe.comp measurable_snd)).aemeasurable]
        dsimp only
        rw [lintegral_const, mul_comm]
    _ = _ := by
        have hw := lintegral_withDensity_eq_lintegral_mul (Measure.comap Subtype.val volume)
          (f := fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ (Module.finrank ℝ E - 1))) (by fun_prop)
          (g := fun y : Ioi (0 : ℝ) => F y) (hF.comp measurable_subtype_coe)
        rw [Measure.volumeIoiPow, hw]
        simp only [Pi.mul_apply, Function.comp_apply]
        rw [lintegral_subtype_comap measurableSet_Ioi (fun y : ℝ => ENNReal.ofReal (y ^ (Module.finrank ℝ E - 1)) * F y)]

theorem finrank_ck (k : ℕ) : Module.finrank ℝ (EuclideanSpace ℂ (Fin k)) = 2 * k := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin k)), Complex.finrank_real_complex,
    finrank_euclideanSpace, Fintype.card_fin]

theorem lintegral_norm_ck (k : ℕ) (hk : 1 ≤ k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y : EuclideanSpace ℂ (Fin k), F ‖y‖ = ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial) *
      ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (2 * k - 1)) * F ρ := by
  have : Nontrivial (EuclideanSpace ℂ (Fin k)) := by
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    infer_instance
  rw [lintegral_fun_norm volume F hF, finrank_ck, Measure.toSphere_apply_univ, finrank_ck,
    InnerProductSpace.volume_ball, finrank_ck]
  congr 1
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hG : Real.Gamma ((↑(2 * (n + 1)) : ℝ) / 2 + 1) = ((n + 1).factorial : ℝ) := by
    rw [show ((↑(2 * (n + 1)) : ℝ) / 2 + 1) = ((n + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  rw [hG, ENNReal.ofReal_one, one_pow, one_mul, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [show ((↑(2 * (n + 1)) : ℝ≥0∞)) = ENNReal.ofReal ((2 * (n + 1) : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp
  try ring

theorem shift_pi (K : ℝ → ℝ≥0∞) :
    ∫⁻ φ in Ioo (-Real.pi) Real.pi, K (φ + Real.pi) = ∫⁻ θ in Ioc 0 (2 * Real.pi), K θ := by
  rw [← lintegral_indicator measurableSet_Ioo,
    ← setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)),
    ← lintegral_indicator measurableSet_Ioo,
    ← lintegral_add_right_eq_self (fun θ => (Ioo 0 (2 * Real.pi)).indicator K θ) Real.pi]
  congr 1
  funext φ
  by_cases h : φ ∈ Ioo (-Real.pi) Real.pi
  · have h' : φ + Real.pi ∈ Ioo 0 (2 * Real.pi) := ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [indicator_of_mem h, indicator_of_mem h']
  · have h' : φ + Real.pi ∉ Ioo 0 (2 * Real.pi) := fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩
    rw [indicator_of_notMem h, indicator_of_notMem h']

theorem lintegral_polar (Ψ : ℂ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ ζ, Ψ ζ = ∫⁻ R in Ioi (0 : ℝ), ENNReal.ofReal R *
      ∫⁻ φ in Ioo (-Real.pi) Real.pi, Ψ (R * (Real.cos φ + Real.sin φ * Complex.I)) := by
  have hm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * Ψ (p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I)) := by
    fun_prop
  rw [← Complex.lintegral_comp_polarCoord_symm,
    show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  simp only [Complex.polarCoord_symm_apply, smul_eq_mul]
  rw [lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun R => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem subst_R (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (X : ℝ → ℝ≥0∞)
    (hX : ∀ R ∈ Ioo 0 (Real.sqrt (T * T')), X R = 0) :
    ∫⁻ R in Ioi 0, X R = ∫⁻ ρ in Ioi 0,
      ENNReal.ofReal (|T * ρ / Real.sqrt (T * (ρ ^ 2 + T'))|) * X (Real.sqrt (T * (ρ ^ 2 + T'))) := by
  set q := Real.sqrt (T * T') with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hTT : 0 < T * T' := mul_pos hT hT'

  have e1 : ∫⁻ R in Ioi 0, X R = ∫⁻ R in Ioi q, X R := by
    rw [← Ioc_union_Ioi_eq_Ioi hq0, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl),
      ← setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := q)),
      setLIntegral_congr_fun measurableSet_Ioo (fun R hR => hX R hR), lintegral_zero, zero_add]
  rw [e1]
  set f : ℝ → ℝ := fun ρ => Real.sqrt (T * (ρ ^ 2 + T')) with hf
  have hpos : ∀ ρ : ℝ, 0 < T * (ρ ^ 2 + T') := fun ρ => by positivity
  have himage : f '' Ioi 0 = Ioi q := by
    ext R
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      simp only [mem_Ioi] at hρ ⊢
      apply Real.sqrt_lt_sqrt hTT.le
      have : 0 < T * ρ ^ 2 := by positivity
      nlinarith
    · intro hR
      simp only [mem_Ioi] at hR
      have hR0 : 0 < R := lt_of_le_of_lt hq0 hR
      have hR2 : T * T' < R ^ 2 := by
        have := (Real.sqrt_lt' hR0).1 hR
        linarith
      have hd : 0 < R ^ 2 / T - T' := by
        rw [sub_pos, lt_div_iff₀ hT]; linarith
      refine ⟨Real.sqrt (R ^ 2 / T - T'), Real.sqrt_pos.2 hd, ?_⟩
      simp only [hf]
      rw [Real.sq_sqrt hd.le, show T * (R ^ 2 / T - T' + T') = R ^ 2 by field_simp; ring,
        Real.sqrt_sq hR0.le]
  have hderiv : ∀ ρ ∈ Ioi (0 : ℝ), HasDerivWithinAt f (T * ρ / Real.sqrt (T * (ρ ^ 2 + T'))) (Ioi 0) ρ := by
    intro ρ hρ
    have h1 : HasDerivAt (fun x : ℝ => T * (x ^ 2 + T')) (T * (2 * ρ)) ρ := by
      have := ((hasDerivAt_pow 2 ρ).add_const T').const_mul T
      simpa using this
    have h2 := h1.sqrt (hpos ρ).ne'
    refine (h2.congr_deriv ?_).hasDerivWithinAt
    have : Real.sqrt (T * (ρ ^ 2 + T')) ≠ 0 := (Real.sqrt_pos.2 (hpos ρ)).ne'
    field_simp
  have hinj : InjOn f (Ioi 0) := by
    intro a ha b hb hab
    simp only [hf] at hab
    rw [Real.sqrt_inj (hpos a).le (hpos b).le] at hab
    have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    have h2 : a ^ 2 = b ^ 2 := by
      have := mul_left_cancel₀ hT.ne' hab
      linarith
    exact le_antisymm (by nlinarith) (by nlinarith)
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj X]

end PI.RhsWLim.W.PH

namespace PI.RhsWLim.W

open PI.RhsWLim PH

theorem polarHyp : PolarHyp := by
  intro k T T' hk hT hT' g hg
  have hs0 : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hTT : 0 < T * T' := mul_pos hT hT'
  set H : ℝ → ℝ≥0∞ := fun ρ => ∫⁻ θ in Ioc 0 (2 * Real.pi),
    g ρ ((Real.sqrt (ρ ^ 2 + T') : ℂ) * Complex.exp (θ * Complex.I)) with hHdef
  have hH : Measurable H := by
    have hm : Measurable fun p : ℝ × ℝ =>
        g p.1 ((Real.sqrt (p.1 ^ 2 + T') : ℂ) * Complex.exp (p.2 * Complex.I)) :=
      hg.comp (measurable_fst.prodMk (by fun_prop))
    exact hm.lintegral_prod_right'
  have eL : hypMeas k T' (fun v => g ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) =
      1 / 2 * ∫⁻ y : EuclideanSpace ℂ (Fin k), H ‖y‖ := rfl
  rw [eL, lintegral_norm_ck k hk H hH]
  set Hh : ℝ → ℝ≥0∞ := fun R => ∫⁻ θ in Ioc 0 (2 * Real.pi),
    g (Real.sqrt ((R ^ 2 - T * T') / T)) (((R / Real.sqrt T : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) with hHh
  set wR : ℝ → ℝ := fun R => if T * T' ≤ R ^ 2 then (R ^ 2 - T * T') ^ (k - 1) else 0 with hwR
  have hw : Measurable fun ζ : ℂ => zWeight k T T' ζ := by
    unfold zWeight
    exact Measurable.ite (measurableSet_le measurable_const Complex.continuous_normSq.measurable)
      ((Complex.continuous_normSq.sub continuous_const).pow _).measurable measurable_const
  have hΨ : Measurable fun ζ : ℂ => ENNReal.ofReal (zWeight k T T' ζ) *
      g (Real.sqrt ((Complex.normSq ζ - T * T') / T)) (-(ζ / (Real.sqrt T : ℂ))) := by
    refine (ENNReal.measurable_ofReal.comp hw).mul (hg.comp (Measurable.prodMk ?_ ?_))
    · exact (Real.continuous_sqrt.comp ((Complex.continuous_normSq.sub continuous_const).div_const T)).measurable
    · exact (continuous_id.div_const _).neg.measurable
  rw [lintegral_polar _ hΨ]
  have eP : ∀ R ∈ Ioi (0 : ℝ), ENNReal.ofReal R * ∫⁻ φ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal (zWeight k T T' (R * (Real.cos φ + Real.sin φ * Complex.I))) *
        g (Real.sqrt ((Complex.normSq (R * (Real.cos φ + Real.sin φ * Complex.I)) - T * T') / T))
          (-((R * (Real.cos φ + Real.sin φ * Complex.I)) / (Real.sqrt T : ℂ))) =
      ENNReal.ofReal R * (ENNReal.ofReal (wR R) * Hh R) := by
    intro R hR
    have hn : ∀ φ : ℝ, Complex.normSq (R * (Real.cos φ + Real.sin φ * Complex.I)) = R ^ 2 := by
      intro φ
      rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_add_mul_I, Real.cos_sq_add_sin_sq]; ring
    have hc : ∀ φ : ℝ, -((R * (Real.cos φ + Real.sin φ * Complex.I)) / (Real.sqrt T : ℂ)) =
        ((R / Real.sqrt T : ℝ) : ℂ) * Complex.exp (((φ + Real.pi : ℝ) : ℂ) * Complex.I) := by
      intro φ
      rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_mul_I, Complex.exp_pi_mul_I]
      push_cast
      ring
    have hz : ∀ φ : ℝ, zWeight k T T' (R * (Real.cos φ + Real.sin φ * Complex.I)) = wR R := by
      intro φ; simp only [zWeight, hn, hwR]
    simp_rw [hn, hc, hz]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 2
    exact shift_pi (fun θ => g (Real.sqrt ((R ^ 2 - T * T') / T))
      (((R / Real.sqrt T : ℝ) : ℂ) * Complex.exp (θ * Complex.I)))
  rw [setLIntegral_congr_fun measurableSet_Ioi eP]
  rw [subst_R T T' hT hT' (fun R => ENNReal.ofReal R * (ENNReal.ofReal (wR R) * Hh R)) (fun R hR => by
      have h : ¬ T * T' ≤ R ^ 2 := by
        have := (Real.lt_sqrt hR.1.le).1 hR.2
        linarith
      simp [hwR, h])]
  have eS : ∀ ρ ∈ Ioi (0 : ℝ), ENNReal.ofReal (|T * ρ / Real.sqrt (T * (ρ ^ 2 + T'))|) *
      (ENNReal.ofReal (Real.sqrt (T * (ρ ^ 2 + T'))) *
        (ENNReal.ofReal (wR (Real.sqrt (T * (ρ ^ 2 + T')))) * Hh (Real.sqrt (T * (ρ ^ 2 + T'))))) =
      ENNReal.ofReal (T ^ k) * (ENNReal.ofReal (ρ ^ (2 * k - 1)) * H ρ) := by
    intro ρ hρ
    have hρ0 : (0 : ℝ) < ρ := hρ
    have hp : 0 < T * (ρ ^ 2 + T') := by positivity
    set F := Real.sqrt (T * (ρ ^ 2 + T')) with hF
    have hF0 : 0 < F := Real.sqrt_pos.2 hp
    have hF2 : F ^ 2 = T * (ρ ^ 2 + T') := Real.sq_sqrt hp.le
    have hwF : wR F = (T * ρ ^ 2) ^ (k - 1) := by
      have hle : T * T' ≤ F ^ 2 := by
        rw [hF2]; have : 0 ≤ T * ρ ^ 2 := by positivity
        linarith
      simp only [hwR]
      rw [if_pos hle, hF2]
      congr 1; ring
    have hHF : Hh F = H ρ := by
      have h1 : Real.sqrt ((F ^ 2 - T * T') / T) = ρ := by
        rw [hF2, show (T * (ρ ^ 2 + T') - T * T') / T = ρ ^ 2 by field_simp; ring, Real.sqrt_sq hρ0.le]
      have h2 : F / Real.sqrt T = Real.sqrt (ρ ^ 2 + T') := by
        rw [hF, Real.sqrt_mul hT.le, mul_div_cancel_left₀ _ hs0.ne']
      simp only [hHh, hHdef]
      rw [h1, h2]
    rw [hwF, hHF, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul (pow_nonneg hT.le k)]
    congr 2
    rw [abs_of_pos (by positivity), div_mul_cancel₀ _ hF0.ne']
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, Nat.add_sub_cancel]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi eS, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have h12 : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [one_div, one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [h12, ← ENNReal.ofReal_mul (by norm_num)]
  congr 2
  field_simp

end PI.RhsWLim.W
