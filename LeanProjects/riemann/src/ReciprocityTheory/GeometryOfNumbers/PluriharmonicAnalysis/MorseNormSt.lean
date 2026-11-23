import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.PolydiscSt

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Filter Topology

theorem morse_normal_bound {D : ℕ} {ρ₀ C : ℝ} (hC : 0 ≤ C) (lam : Fin D → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (φ ν : (Fin D → ℂ) → ℝ)
    (hφc : ContinuousOn φ (Metric.ball 0 ρ₀)) (hνc : ContinuousOn ν (Metric.ball 0 ρ₀))
    (hφ : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, φ z ≤ ∑ j, lam j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3)
    (hν : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 1 - C * ‖z‖ ≤ ν z)
    (f : (Fin D → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ₀))
    (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 < R) (hRn : R / Real.sqrt n < ρ₀)
    (hCR : C * (R / Real.sqrt n) < 1) :
    ‖f 0‖ ^ 2 * ((∏ j, discI (lam j) R) / (n : ℝ) ^ D) *
        (Real.exp (-(C * R ^ 3 / Real.sqrt n)) * (1 - C * (R / Real.sqrt n))) ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) (R / Real.sqrt n),
        ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
  set s := Real.sqrt (n : ℝ) with hs_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.mpr hn'
  have hss : s * s = n := Real.mul_self_sqrt hn'.le
  set r := R / s with hr_def
  have hr : 0 < r := div_pos hR hs
  set K := Real.exp (-(C * R ^ 3 / s)) * (1 - C * r) with hK
  have hK0 : 0 ≤ K := mul_nonneg (Real.exp_pos _).le (by linarith)
  have hsub : Metric.closedBall (0 : Fin D → ℂ) r ⊆ Metric.ball 0 ρ₀ :=
    Metric.closedBall_subset_ball hRn

  have hcont : ContinuousOn (fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z)
      (Metric.closedBall (0 : Fin D → ℂ) r) := by
    have h1 : ContinuousOn f (Metric.closedBall (0 : Fin D → ℂ) r) := hf.continuousOn.mono hsub
    have h2 : ContinuousOn φ (Metric.closedBall (0 : Fin D → ℂ) r) := hφc.mono hsub
    have h3 : ContinuousOn ν (Metric.closedBall (0 : Fin D → ℂ) r) := hνc.mono hsub
    exact ((h1.norm.pow 2).mul ((continuousOn_const.mul h2).neg.rexp)).mul h3
  have hint : IntegrableOn (fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z)
      (Metric.ball (0 : Fin D → ℂ) r) :=
    (hcont.integrableOn_compact (isCompact_closedBall 0 r)).mono_set Metric.ball_subset_closedBall

  have hpt : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) r,
      K * (‖f z‖ ^ 2 * Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2)) ≤
        ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
    intro z hz
    have hzρ : z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀ := hsub (Metric.ball_subset_closedBall hz)
    have hzr : ‖z‖ < r := by simpa using hz
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
    have hz3 : ‖z‖ ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hz0 hzr.le 3
    have hnr : (n : ℝ) * r ^ 3 = R ^ 3 / s := by
      rw [hr_def, ← hss]; field_simp
    have hφn : (n : ℝ) * φ z ≤ ∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2 + C * R ^ 3 / s := by
      have := hφ z hzρ
      have e1 : ∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2 = (n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2 := by
        rw [Finset.mul_sum]; congr 1; ext j; ring
      have e2 : C * R ^ 3 / s = C * ((n : ℝ) * r ^ 3) := by rw [hnr]; ring
      rw [e1, e2]
      have : (n : ℝ) * φ z ≤ (n : ℝ) * (∑ j, lam j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3) :=
        mul_le_mul_of_nonneg_left this hn'.le
      nlinarith [mul_le_mul_of_nonneg_left hz3 (mul_nonneg hC hn'.le)]
    have hexp : Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2) * Real.exp (-(C * R ^ 3 / s)) ≤
        Real.exp (-((n : ℝ) * φ z)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have hνz : 1 - C * r ≤ ν z := by
      have := hν z hzρ
      nlinarith [mul_le_mul_of_nonneg_left hzr.le hC]
    have hCr : 0 ≤ 1 - C * r := by linarith
    have hf2 : 0 ≤ ‖f z‖ ^ 2 := by positivity
    calc K * (‖f z‖ ^ 2 * Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2))
        = ‖f z‖ ^ 2 * (Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2) *
            Real.exp (-(C * R ^ 3 / s))) * (1 - C * r) := by rw [hK]; ring
      _ ≤ ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hexp hf2) hνz hCr
        exact mul_nonneg hf2 (Real.exp_pos _).le
  have hmono : ∫ z in Metric.ball (0 : Fin D → ℂ) r,
      K * (‖f z‖ ^ 2 * Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2)) ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) r, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
    apply integral_mono_of_nonneg _ hint
    · exact ae_restrict_of_forall_mem measurableSet_ball hpt
    · exact ae_of_all _ (fun z => mul_nonneg hK0 (mul_nonneg (by positivity) (Real.exp_pos _).le))
  rw [integral_const_mul] at hmono
  have hgauss := polydisc_gauss_le hr hRn f hf (fun j => (n : ℝ) * lam j)
  have hscale : ∀ j, discI ((n : ℝ) * lam j) r = discI (lam j) R / n := by
    intro j; rw [hr_def, hs_def]; exact discI_scale (hlam j) hR.le hn'
  have hprod : ∏ j, discI ((n : ℝ) * lam j) r = (∏ j, discI (lam j) R) / (n : ℝ) ^ D := by
    simp_rw [hscale]; rw [Finset.prod_div_distrib]; simp
  rw [hprod] at hgauss
  calc ‖f 0‖ ^ 2 * ((∏ j, discI (lam j) R) / (n : ℝ) ^ D) *
        (Real.exp (-(C * R ^ 3 / s)) * (1 - C * (R / s)))
      = K * (‖f 0‖ ^ 2 * ((∏ j, discI (lam j) R) / (n : ℝ) ^ D)) := by rw [hK]; ring
    _ ≤ K * ∫ z in Metric.ball (0 : Fin D → ℂ) r,
          ‖f z‖ ^ 2 * Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hgauss hK0
    _ ≤ _ := hmono

theorem morse_normal_uniform {D : ℕ} {ρ₀ C Λ : ℝ} (hρ₀ : 0 < ρ₀) (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, 0 < n → ∀ (lam : Fin D → ℝ) (φ ν : (Fin D → ℂ) → ℝ)
      (f : (Fin D → ℂ) → ℂ), (∀ j, 0 ≤ lam j ∧ lam j ≤ Λ) →
      ContinuousOn φ (Metric.ball 0 ρ₀) → ContinuousOn ν (Metric.ball 0 ρ₀) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, φ z ≤ ∑ j, lam j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 1 - C * ‖z‖ ≤ ν z) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 0 ≤ ν z) →
      DifferentiableOn ℂ f (Metric.ball 0 ρ₀) →
      IntegrableOn (fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z)
        (Metric.ball (0 : Fin D → ℂ) ρ₀) →
      ‖f 0‖ ^ 2 ≤ M * (n : ℝ) ^ D *
        ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
  set R := min (ρ₀ / 2) (1 / (2 * (C + 1))) with hRdef
  have hC1 : 0 < C + 1 := by linarith
  have hR : 0 < R := lt_min (by linarith) (by positivity)
  have hRρ : R < ρ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hCR : C * R ≤ 1 / 2 := by
    have h1 : R ≤ 1 / (2 * (C + 1)) := min_le_right _ _
    have h2 : (C + 1) * R ≤ 1 / 2 := by
      calc (C + 1) * R ≤ (C + 1) * (1 / (2 * (C + 1))) := mul_le_mul_of_nonneg_left h1 hC1.le
        _ = 1 / 2 := by field_simp
    nlinarith
  set G := discI Λ R ^ D with hG
  have hG0 : 0 < G := pow_pos (discI_pos hΛ hR) D
  set E := Real.exp (-(C * R ^ 3)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨2 / (G * E), by positivity, ?_⟩
  intro n hnpos lam φ ν f hlam hφc hνc hφ hν hν0 hf hint
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hnpos)
  have hRs : R / Real.sqrt n ≤ R := div_le_self hR.le hs1
  have hφ' : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀,
      φ z ≤ ∑ j, (fun _ => Λ) j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3 := by
    intro z hz
    refine (hφ z hz).trans ?_
    gcongr with j
    exact (hlam j).2
  have hCRs : C * (R / Real.sqrt n) ≤ C * R := mul_le_mul_of_nonneg_left hRs hC
  have B := morse_normal_bound hC (fun _ => Λ) (fun _ => hΛ) φ ν hφc hνc hφ' hν f hf n hnpos R hR
    (hRs.trans_lt hRρ) (by linarith)
  have hprod : ∏ _j : Fin D, discI Λ R = G := by simp [hG]
  rw [hprod] at B
  set h := Real.exp (-(C * R ^ 3 / Real.sqrt n)) * (1 - C * (R / Real.sqrt n)) with hh
  have hhE : E / 2 ≤ h := by
    have e1 : E ≤ Real.exp (-(C * R ^ 3 / Real.sqrt n)) := by
      rw [hE]; apply Real.exp_le_exp.mpr
      have : C * R ^ 3 / Real.sqrt n ≤ C * R ^ 3 := div_le_self (by positivity) hs1
      linarith
    have e2 : (1 : ℝ) / 2 ≤ 1 - C * (R / Real.sqrt n) := by linarith
    calc E / 2 = E * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul e1 e2 (by norm_num) (Real.exp_pos _).le
  have hh0 : 0 < h := lt_of_lt_of_le (by positivity) hhE
  have hsub : Metric.ball (0 : Fin D → ℂ) (R / Real.sqrt n) ⊆ Metric.ball 0 ρ₀ :=
    Metric.ball_subset_ball (hRs.trans hRρ.le)
  have hI : ∫ z in Metric.ball (0 : Fin D → ℂ) (R / Real.sqrt n),
        ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
    apply setIntegral_mono_set hint
    · exact ae_restrict_of_forall_mem measurableSet_ball (fun z hz =>
        mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (hν0 z hz))
    · exact Eventually.of_forall hsub
  set I := ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball (fun z hz =>
        mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (hν0 z hz))
  have hnD : (0 : ℝ) < (n : ℝ) ^ D := pow_pos hn' D
  have hB' : ‖f 0‖ ^ 2 * (G / (n : ℝ) ^ D) * h ≤ I := B.trans hI
  have e : ‖f 0‖ ^ 2 = (‖f 0‖ ^ 2 * (G / (n : ℝ) ^ D) * h) * ((n : ℝ) ^ D * (G⁻¹ / h)) := by
    field_simp
  have key : G⁻¹ / h ≤ 2 / (G * E) := by
    rw [div_le_div_iff₀ hh0 (by positivity)]
    have : G⁻¹ * (G * E) = E := by field_simp
    nlinarith
  calc ‖f 0‖ ^ 2 = _ := e
    _ ≤ I * ((n : ℝ) ^ D * (G⁻¹ / h)) :=
        mul_le_mul_of_nonneg_right hB' (by positivity)
    _ ≤ I * ((n : ℝ) ^ D * (2 / (G * E))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hnD.le) hI0
    _ = _ := by ring

end ReciprocityTheory.GeometryOfNumbersTheory
