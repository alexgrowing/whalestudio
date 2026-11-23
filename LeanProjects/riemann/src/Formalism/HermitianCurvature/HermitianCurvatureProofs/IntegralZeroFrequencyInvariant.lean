import Formalism.HermitianCurvature.StatementB

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.B1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem semi : SeminormIneq := by
  intro V _ _ β hβ hnn x y
  obtain ⟨ba1, ba2, bs1, bs2⟩ := hβ
  have hre : ∀ z, 0 ≤ (β z z).re := by
    intro z
    exact (hnn z).2
  have hexp : ∀ t : ℝ, (β (x + ((-t : ℝ) : ℂ) • y) (x + ((-t : ℝ) : ℂ) • y)).re =
      (β y y).re * (t * t) + (-(β x y + β y x).re) * t + (β x x).re := by
    intro t
    simp only [ba1, ba2, bs1, bs2, Complex.conj_ofReal, Complex.add_re, Complex.re_ofReal_mul]
    ring
  have hq : ∀ t : ℝ, 0 ≤ (β y y).re * (t * t) + (-(β x y + β y x).re) * t + (β x x).re := by
    intro t
    rw [← hexp t]
    exact hre _
  have hd := discrim_le_zero hq
  simp only [discrim] at hd
  have h1 := hexp 1
  rw [show x + ((-(1 : ℝ) : ℝ) : ℂ) • y = x - y by
    rw [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, sub_eq_add_neg]] at h1
  rw [h1]
  have ha := hre x
  have hb := hre y
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hpa := Real.sqrt_nonneg (β x x).re
  have hpb := Real.sqrt_nonneg (β y y).re
  nlinarith [mul_nonneg hpa hpb, sq_nonneg (Real.sqrt (β x x).re - Real.sqrt (β y y).re),
    sq_nonneg ((β x y + β y x).re + 2 * (Real.sqrt (β x x).re * Real.sqrt (β y y).re))]

theorem core (hsemi : SeminormIneq) (hpol : Polarisation) : FormCoreC := by
  intro V _ _ W β βi hβ hβi hnn hle hW
  refine hpol V W β βi hβ hβi ?_
  intro x hx
  obtain ⟨Φ, c, t₀, _h0, hc0, hcc, hlim, U, hU, hae⟩ := hW x hx
  have hsq : ∀ t, (Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) ^ 2 ≤
      (βi (Φ t - x) (Φ t - x)).re :=
    fun t => (hsemi V β hβ hnn (Φ t) x).trans (hle _)
  have hT1 : Tendsto (fun t => (Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) ^ 2)
      (𝓝 t₀) (𝓝 0) :=
    squeeze_zero (fun t => sq_nonneg _) hsq hlim
  have hT2 : Tendsto (fun t => Real.sqrt (β (Φ t) (Φ t)).re) (𝓝 t₀)
      (𝓝 (Real.sqrt (β x x).re)) := by
    have h' : Tendsto (fun t => Real.sqrt (β (Φ t) (Φ t)).re - Real.sqrt (β x x).re) (𝓝 t₀)
        (𝓝 0) := by
      have h2 := hT1.sqrt
      rw [Real.sqrt_zero] at h2
      simp only [Real.sqrt_sq_eq_abs] at h2
      exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h2
    simpa using h'.add_const (Real.sqrt (β x x).re)
  have e : ∀ t, Real.sqrt (β (Φ t) (Φ t)).re ^ 2 = (β (Φ t) (Φ t)).re :=
    fun t => Real.sq_sqrt (hnn _).2
  have hT3 : Tendsto (fun t => (β (Φ t) (Φ t)).re) (𝓝 t₀) (𝓝 (β x x).re) := by
    simpa only [e, Real.sq_sqrt (hnn x).2] using hT2.pow 2
  have hNe : (ae (volume.restrict U) ⊓ 𝓝 t₀).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s₁ hs₁ s₂ hs₂
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hO : t₀ ∈ interior (s₂ ∩ U) := mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hs₂ hU)
    have hpos : 0 < volume (interior (s₂ ∩ U)) := isOpen_interior.measure_pos volume ⟨t₀, hO⟩
    have hsub : interior (s₂ ∩ U) ⊆ s₁ᶜ := by
      intro t ht hts
      have hmem : t ∈ s₁ ∩ s₂ := ⟨hts, (interior_subset ht).1⟩
      rw [hemp] at hmem
      exact hmem
    have h0' : volume.restrict U s₁ᶜ = 0 := mem_ae_iff.mp hs₁
    have hle2 : volume.restrict U (interior (s₂ ∩ U)) ≤ volume.restrict U s₁ᶜ := measure_mono hsub
    rw [h0', Measure.restrict_apply isOpen_interior.measurableSet,
      Set.inter_eq_left.mpr (interior_subset.trans Set.inter_subset_right)] at hle2
    exact lt_irrefl _ (hpos.trans_le hle2)
  have hcL : Tendsto c (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 (βi x x)) := by
    rw [← hc0]
    exact hcc.tendsto.mono_left inf_le_right
  have hbL : Tendsto (fun t => β (Φ t) (Φ t)) (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 (βi x x)) :=
    hcL.congr' ((Filter.Eventually.filter_mono inf_le_left hae).mono fun t ht => ht.symm)
  have hre : (β x x).re = (βi x x).re :=
    tendsto_nhds_unique (hT3.mono_left inf_le_right) ((Complex.continuous_re.tendsto _).comp hbL)
  have him : (0 : ℝ) = (βi x x).im := by
    have e2 : (fun t => (β (Φ t) (Φ t)).im) = fun _ => (0 : ℝ) := funext fun t => (hnn (Φ t)).1
    have h1 : Tendsto (fun t => (β (Φ t) (Φ t)).im) (ae (volume.restrict U) ⊓ 𝓝 t₀) (𝓝 0) := by
      rw [e2]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 ((Complex.continuous_im.tendsto _).comp hbL)
  exact Complex.ext hre (by rw [(hnn x).1, ← him])

theorem polar : Polarisation := by
  intro V _ _ W β γ hβ hγ hW x hx y hy
  obtain ⟨ba1, ba2, bs1, bs2⟩ := hβ
  obtain ⟨ga1, ga2, gs1, gs2⟩ := hγ
  have hxy := hW (x + y) (W.add_mem hx hy)
  have hxiy := hW (x + Complex.I • y) (W.add_mem hx (W.smul_mem _ hy))
  have hxx := hW x hx
  have hyy := hW y hy
  simp only [ba1, ba2, ga1, ga2] at hxy
  simp only [ba1, ba2, bs1, bs2, ga1, ga2, gs1, gs2, Complex.conj_I] at hxiy
  linear_combination (1 / 2 : ℂ) * (hxy - hxx - hyy) +
    (Complex.I / 2) * (hxiy - hxx + Complex.I ^ 2 * hyy) -
    ((β y x - γ y x - (β x y - γ x y)) / 2) * Complex.I_sq

theorem coreC : FormCoreC := core semi polar

theorem core0 : FormCore := by
  intro V _ _ W β βi hβ hβi hnn hle hW
  refine coreC V W β βi hβ hβi hnn hle ?_
  intro x hx
  obtain ⟨Φ, t₀, h0, hc, ht, U, hU, hae⟩ := hW x hx
  exact ⟨Φ, fun t => βi (Φ t) (Φ t), t₀, h0, by simp only [h0], hc, ht, U, hU, hae⟩

theorem fatou : FatouParam := by
  intro Q _ μ E _ U J c hU hJm hJc hc hae τ hτ
  have hNe : (ae (volume.restrict U) ⊓ 𝓝 τ).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s₁ hs₁ s₂ hs₂
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hO : τ ∈ interior (s₂ ∩ U) :=
      mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hs₂ (hU.mem_nhds hτ))
    have hpos : 0 < volume (interior (s₂ ∩ U)) := isOpen_interior.measure_pos volume ⟨τ, hO⟩
    have hsub : interior (s₂ ∩ U) ⊆ s₁ᶜ := by
      intro t ht hts
      have hmem : t ∈ s₁ ∩ s₂ := ⟨hts, (interior_subset ht).1⟩
      rw [hemp] at hmem
      exact hmem
    have h0' : volume.restrict U s₁ᶜ = 0 := mem_ae_iff.mp hs₁
    have hle2 : volume.restrict U (interior (s₂ ∩ U)) ≤ volume.restrict U s₁ᶜ := measure_mono hsub
    rw [h0', Measure.restrict_apply isOpen_interior.measurableSet,
      Set.inter_eq_left.mpr (interior_subset.trans Set.inter_subset_right)] at hle2
    exact lt_irrefl _ (hpos.trans_le hle2)
  have hex : ∀ n : ℕ, ∃ σ, σ ∈ Metric.ball τ (1 / ((n : ℝ) + 1)) ∩ U ∧
      ∫⁻ q, ‖J σ q‖ₑ ^ 2 ∂μ = ENNReal.ofReal (c σ) := by
    intro n
    have h1 : Metric.ball τ (1 / ((n : ℝ) + 1)) ∩ U ∈ 𝓝 τ :=
      Filter.inter_mem (Metric.ball_mem_nhds τ (by positivity)) (hU.mem_nhds hτ)
    obtain ⟨σ, hσ1, hσ2⟩ := Filter.inf_neBot_iff.mp hNe hae h1
    exact ⟨σ, hσ2, hσ1⟩
  choose σ hσ hσeq using hex
  have hσT : Tendsto σ atTop (𝓝 τ) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact (Metric.mem_ball.mp (hσ n).1).le
  have hσW : Tendsto σ atTop (𝓝[U] τ) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσT, Filter.Eventually.of_forall fun n => (hσ n).2⟩
  have hpt : ∀ᵐ q ∂μ, Tendsto (fun n => ‖J (σ n) q‖ₑ ^ 2) atTop (𝓝 (‖J τ q‖ₑ ^ 2)) := by
    filter_upwards [hJc] with q hq
    have h2 := ((hq τ hτ).tendsto).comp hσW
    exact ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp h2)
  have hcT : Tendsto (fun n => ENNReal.ofReal (c (σ n))) atTop (𝓝 (ENNReal.ofReal (c τ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((hc τ hτ).tendsto.comp hσW)
  calc ∫⁻ q, ‖J τ q‖ₑ ^ 2 ∂μ = ∫⁻ q, liminf (fun n => ‖J (σ n) q‖ₑ ^ 2) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpt] with q hq
        exact hq.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ q, ‖J (σ n) q‖ₑ ^ 2 ∂μ) atTop := by
        apply lintegral_liminf_le'
        intro n
        exact ((hJm (σ n) (hσ n).2).enorm).pow_const 2
    _ = liminf (fun n => ENNReal.ofReal (c (σ n))) atTop := by
        simp only [hσeq]
    _ = ENNReal.ofReal (c τ) := hcT.liminf_eq

theorem ibp : RegIBP := by
  intro h hh hc x
  set e : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) with he
  have hed : ∀ t, HasDerivAt e (Complex.I * x * e t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * ((x * t : ℝ) : ℂ)) (Complex.I * x) t := by
      have h2 : HasDerivAt (fun t : ℝ => ((x * t : ℝ) : ℂ)) ((x : ℝ) : ℂ) t := by
        have := ((hasDerivAt_id t).const_mul x).ofReal_comp
        simpa using this
      exact h2.const_mul _
    have := h1.cexp
    simpa [he, mul_comm, mul_left_comm, mul_assoc] using this
  have hec : Continuous e := by
    rw [he]; fun_prop
  have hd1 : ContDiff ℝ 1 (deriv h) := by
    have : ContDiff ℝ (1 + 1) h := by simpa [one_add_one_eq_two] using hh
    exact ((contDiff_succ_iff_deriv).1 this).2.2
  have hh0 : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hh1 : Differentiable ℝ (deriv h) := hd1.differentiable (by norm_num)
  have c0 : Continuous h := hh.continuous
  have c1 : Continuous (deriv h) := hd1.continuous
  have c2 : Continuous (deriv (deriv h)) := hd1.continuous_deriv (le_refl _)
  have k1 : HasCompactSupport (deriv h) := hc.deriv
  have k2 : HasCompactSupport (deriv (deriv h)) := k1.deriv
  have i2 : iteratedDeriv 2 h = deriv (deriv h) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have I0 : Integrable (fun t => e t * h t) := (hec.mul c0).integrable_of_hasCompactSupport hc.mul_left
  have I1 : Integrable (fun t => e t * deriv h t) := (hec.mul c1).integrable_of_hasCompactSupport k1.mul_left
  have I2 : Integrable (fun t => e t * deriv (deriv h) t) := (hec.mul c2).integrable_of_hasCompactSupport k2.mul_left
  have J0 : Integrable (fun t => (Complex.I * x * e t) * h t) := by
    simpa [mul_assoc] using I0.const_mul (Complex.I * x)
  have J1 : Integrable (fun t => (Complex.I * x * e t) * deriv h t) := by
    simpa [mul_assoc] using I1.const_mul (Complex.I * x)
  have s1 : (∫ t, e t * deriv (deriv h) t) = - ∫ t, (Complex.I * x * e t) * deriv h t :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hed t) (fun t _ => (hh1 t).hasDerivAt) I2 J1 I1
  have s2 : (∫ t, e t * deriv h t) = - ∫ t, (Complex.I * x * e t) * h t :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hed t) (fun t _ => (hh0 t).hasDerivAt) I1 J0 I0
  have m1 : (∫ t, (Complex.I * x * e t) * deriv h t) = Complex.I * x * ∫ t, e t * deriv h t := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have m0 : (∫ t, (Complex.I * x * e t) * h t) = Complex.I * x * ∫ t, e t * h t := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have l : (∫ t : ℝ, (h t - iteratedDeriv 2 h t) * e t) = (∫ t, e t * h t) - ∫ t, e t * deriv (deriv h) t := by
    rw [← integral_sub I0 I2, i2]; congr 1; funext t; ring
  have r : (∫ t : ℝ, h t * e t) = ∫ t, e t * h t := by congr 1; funext t; ring
  rw [l, r, s1, m1, s2, m0]
  push_cast
  linear_combination (-(x:ℂ)^2 * ∫ t, e t * h t) * Complex.I_mul_I

theorem decay (hibp : RegIBP) : TestDecay := by
  unfold TestDecay
  unfold RegIBP at hibp
  intro wh hwh
  unfold om
  unfold IsTest at hwh
  obtain ⟨hcd, hcs, _⟩ := hwh
  have hcd' : ContDiff ℝ 2 (fun t : ℝ => (wh t : ℂ)) := by
    first
    | exact Complex.ofRealCLM.contDiff.comp hcd
    | fun_prop
  have hcs' : HasCompactSupport (fun t : ℝ => (wh t : ℂ)) := hcs.comp_left Complex.ofReal_zero
  have hgc : Continuous (fun t : ℝ => (wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t) :=
    hcd'.continuous.sub (hcd'.continuous_iteratedDeriv 2 (by norm_num))
  have hgs : HasCompactSupport
      (fun t : ℝ => (wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t) :=
    hcs'.sub (by
      first
      | (rw [iteratedDeriv_succ, iteratedDeriv_one]; exact hcs'.deriv.deriv)
      | (rw [iteratedDeriv_eq_iterate]; exact hcs'.deriv.deriv)
      | exact hcs'.iteratedDeriv 2)
  have hn : ∀ y : ℝ, ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1 := fun y => by
    rw [Complex.norm_exp]
    simp
  refine ⟨2 * ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖, fun x => ?_⟩
  have key := hibp (fun t : ℝ => (wh t : ℂ)) hcd' hcs' x
  beta_reduce at key
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hbound : ‖∫ t, ((wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t) *
      Complex.exp (Complex.I * ↑(x * t))‖ ≤
      ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext t
    rw [norm_mul, hn, mul_one]
  have e2 : ∫ τ, (wh τ : ℂ) * Complex.exp (Complex.I * ↑(τ * x)) =
      ∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t)) := by
    congr 1
    funext t
    rw [mul_comm t x]
  rw [e2]
  have hI : ‖∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t))‖ * (1 + x ^ 2) ≤
      ∫ t, ‖(wh t : ℂ) - iteratedDeriv 2 (fun t : ℝ => (wh t : ℂ)) t‖ := by
    have h3 := congrArg norm key
    rw [norm_mul, Complex.norm_of_nonneg hpos.le] at h3
    rw [mul_comm, ← h3]
    exact hbound
  have hsq : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by
    nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]
  have hq : 0 < (1 + |x|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hq]
  have hm := mul_le_mul_of_nonneg_left hsq
    (norm_nonneg (∫ t, (wh t : ℂ) * Complex.exp (Complex.I * ↑(x * t))))
  nlinarith [hI, hm]

theorem intZero : IntRdZeroInv := by
  intro n μ _ X h hinv hC1 hI hRI
  set E : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => NormedSpace.exp ((t : ℂ) • X) with hE
  have hEcont : Continuous E := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    have h1 : Continuous fun t : ℝ => ((t : ℂ) • X) := by fun_prop
    exact NormedSpace.exp_continuous.comp h1
  have hEadd : ∀ s t : ℝ, E (s + t) = E s * E t := by
    intro s t
    simp only [hE]
    rw [← Matrix.exp_add_of_commute]
    · congr 1; push_cast; rw [add_smul]
    · exact ((Commute.refl X).smul_left _).smul_right _
  have hE0 : E 0 = 1 := by simp [hE]
  set k : (Fin n → Fin n → ℂ) → ℂ := fun g => RdV X h (Matrix.of g) with hk
  set Ψ : (Fin n → Fin n → ℂ) × ℝ → (Fin n → Fin n → ℂ) := fun p => rmulF (E p.2) p.1 with hΨd
  have hΨc : Continuous Ψ := by
    have : Continuous fun p : (Fin n → Fin n → ℂ) × ℝ => (Matrix.of p.1 : Matrix (Fin n) (Fin n) ℂ) * E p.2 :=
      Continuous.matrix_mul continuous_fst (hEcont.comp continuous_snd)
    exact this
  have hΨ : Measurable Ψ := hΨc.measurable
  have hR : ∀ s : ℝ, Measurable (rmulF (E s)) := fun s => hΨ.comp measurable_prodMk_right
  set ν : Measure ℝ := volume.restrict (Set.Ioc 0 1) with hν
  have hq : Measure.QuasiMeasurePreserving Ψ (μ.prod ν) μ := by
    refine ⟨hΨ, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
    rw [Measure.map_apply hΨ hs, Measure.prod_apply_symm (hΨ hs)]
    have : ∀ y : ℝ, μ ((fun x => (x, y)) ⁻¹' (Ψ ⁻¹' s)) = 0 := by
      intro y
      have e : (fun x => (x, y)) ⁻¹' (Ψ ⁻¹' s) = rmulF (E y) ⁻¹' s := rfl
      rw [e, ← Measure.map_apply (hR y) hs, hinv y, h0]
    simp [this]
  have hkR : ∀ s : ℝ, Integrable (fun g => k (rmulF (E s) g)) μ := by
    intro s
    have : Integrable k (μ.map (rmulF (E s))) := by rw [hinv s]; exact hRI
    exact this.comp_measurable (hR s)
  have hkI : ∀ s : ℝ, (∫ g, k (rmulF (E s) g) ∂μ) = ∫ g, k g ∂μ := by
    intro s
    have hm : AEStronglyMeasurable k (μ.map (rmulF (E s))) := by rw [hinv s]; exact hRI.1
    rw [← integral_map (hR s).aemeasurable hm, hinv s]
  have hkN : ∀ s : ℝ, (∫ g, ‖k (rmulF (E s) g)‖ ∂μ) = ∫ g, ‖k g‖ ∂μ := by
    intro s
    have hm : AEStronglyMeasurable (fun g => ‖k g‖) (μ.map (rmulF (E s))) := by rw [hinv s]; exact hRI.1.norm
    rw [← integral_map (hR s).aemeasurable hm, hinv s]
  have hint : Integrable (fun p => k (Ψ p)) (μ.prod ν) := by
    have hm : AEStronglyMeasurable (fun p => k (Ψ p)) (μ.prod ν) := hRI.1.comp_quasiMeasurePreserving hq
    rw [integrable_prod_iff' hm]
    refine ⟨Filter.Eventually.of_forall fun s => hkR s, ?_⟩
    have : (fun y : ℝ => ∫ x, ‖k (Ψ (x, y))‖ ∂μ) = fun _ => ∫ g, ‖k g‖ ∂μ := by
      funext y; exact hkN y
    rw [this]
    exact integrable_const _
  have hswap := integral_integral_swap (f := fun g s => k (Ψ (g, s))) (μ := μ) (ν := ν) hint
  have hrhs : (∫ s, ∫ g, k (Ψ (g, s)) ∂μ ∂ν) = ∫ g, k g ∂μ := by
    have : (fun s : ℝ => ∫ g, k (Ψ (g, s)) ∂μ) = fun _ => ∫ g, k g ∂μ := by
      funext s; exact hkI s
    rw [this]
    simp [hν]
  have hftc : ∀ᵐ g ∂μ, (∫ s, k (Ψ (g, s)) ∂ν) = h (Matrix.of (rmulF (E 1) g)) - h (Matrix.of g) := by
    filter_upwards [hC1] with g hg
    set φ : ℝ → ℂ := fun t => h (Matrix.of g * E t) with hφ
    have hd : ∀ s, deriv φ s = k (Ψ (g, s)) := by
      intro s
      have e1 : k (Ψ (g, s)) = deriv (fun t : ℝ => φ (s + t)) 0 := by
        simp only [hk, RdV, hΨd, hφ]
        congr 1
        funext t
        rw [hEadd, ← mul_assoc]
        rfl
      rw [e1, deriv_comp_const_add, add_zero]
    have hf := intervalIntegral.integral_deriv_eq_sub (f := φ) (a := 0) (b := 1)
      (fun x _ => (hg.differentiable (by norm_num)) x)
      ((hg.continuous_deriv (le_refl _)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_of_le zero_le_one] at hf
    have e2 : (∫ s, k (Ψ (g, s)) ∂ν) = ∫ s in Set.Ioc 0 1, deriv φ s := by
      rw [hν]; congr 1; funext s; exact (hd s).symm
    rw [e2, hf]
    simp only [hφ, hE0, mul_one]
    rfl
  have hhI : (∫ g, h (Matrix.of (rmulF (E 1) g)) ∂μ) = ∫ g, h (Matrix.of g) ∂μ := by
    have hm : AEStronglyMeasurable (fun g => h (Matrix.of g)) (μ.map (rmulF (E 1))) := by rw [hinv 1]; exact hI.1
    rw [← integral_map (hR 1).aemeasurable hm, hinv 1]
  have hhR : Integrable (fun g => h (Matrix.of (rmulF (E 1) g))) μ := by
    have : Integrable (fun g => h (Matrix.of g)) (μ.map (rmulF (E 1))) := by rw [hinv 1]; exact hI
    exact this.comp_measurable (hR 1)
  have hl : (∫ g, ∫ s, k (Ψ (g, s)) ∂ν ∂μ) = 0 := by
    rw [integral_congr_ae hftc, integral_sub hhR hI, hhI, sub_self]
  rw [← hrhs, ← hswap, hl]

end Formalism.FourierDecayAlt.P.B1

namespace Formalism.FourierDecayAlt.P

theorem seminorm_inequality : Formalism.FourierDecayAlt.B.SeminormIneq := B1.semi

theorem bilinear_form_continuity : Formalism.FourierDecayAlt.B.FormCoreC := B1.coreC

theorem bilinear_form_at_zero : Formalism.FourierDecayAlt.B.FormCore := B1.core0

theorem fatou_lemma_in_parameter : Formalism.FourierDecayAlt.B.FatouParam := B1.fatou

theorem integration_by_parts_regularised : Formalism.FourierDecayAlt.B.RegIBP := B1.ibp

theorem test_function_decay : Formalism.FourierDecayAlt.B.TestDecay := B1.decay B1.ibp

theorem integral_zero_frequency_invariant : Formalism.FourierDecayAlt.B.IntRdZeroInv := B1.intZero

end Formalism.FourierDecayAlt.P
