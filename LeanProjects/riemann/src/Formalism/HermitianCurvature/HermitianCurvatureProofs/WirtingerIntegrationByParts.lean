import Formalism.HermitianCurvature.StatementG

namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts

open Formalism.FourierDecayAlt.G MeasureTheory

instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

theorem muPi_eq (β : ℂ) (ι : Type) [Fintype ι] :
    muPi β ι = (Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card ι • (volume : Measure (ι → ℂ)) := by
  unfold muPi
  refine Measure.pi_eq fun s hs => ?_
  simp only [mu, Measure.smul_apply, volume_pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

instance (β : ℂ) (ι : Type) [Fintype ι] : IsFiniteMeasureOnCompacts (muPi β ι) := by
  rw [muPi_eq]; infer_instance

theorem contDiff_smul_of_tsupport {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {φ : E → ℂ} {a : E → V} {Ω : Set E} {n : WithTop ℕ∞}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ n φ Ω) (ha : ContDiff ℝ n a) (hsupp : tsupport a ⊆ Ω) :
    ContDiff ℝ n (fun x => φ x • a x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact (hφ.contDiffAt (hΩ.mem_nhds hx)).smul ha.contDiffAt
  · have hx' : x ∉ tsupport a := fun h => hx (hsupp h)
    have h0 : (fun y => φ y • a y) =ᶠ[nhds x] fun _ => (0 : V) := by
      have := notMem_tsupport_iff_eventuallyEq.mp hx'
      filter_upwards [this] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

theorem tsupport_smul_subset' {E V : Type*} [TopologicalSpace E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : E → ℂ) (a : E → V) :
    tsupport (fun x => φ x • a x) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h; apply hx; simp [h]

section

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem hol_hasDerivAt_line {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (x v : Fin d → ℂ) (ζ : ℂ) (h : x + ζ • v ∈ Ω) :
    HasDerivAt (fun ζ : ℂ => g (x + ζ • v)) (fderiv ℂ g (x + ζ • v) v) ζ := by
  have h1 : HasFDerivAt g (fderiv ℂ g (x + ζ • v)) (x + ζ • v) :=
    (hg.differentiableAt (hΩ.mem_nhds h)).hasFDerivAt
  have h2 : HasDerivAt (fun ζ : ℂ => x + ζ • v) v ζ := by
    simpa using ((hasDerivAt_id ζ).smul_const v).const_add x
  exact h1.comp_hasDerivAt ζ h2

theorem hol_clm_decomp (L : (Fin d → ℂ) →L[ℂ] F) :
    L = ∑ k, (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).smulRight (L (Pi.single k 1)) := by
  ext v
  have hv : v = ∑ k, v k • (Pi.single k (1 : ℂ) : Fin d → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext i
    by_cases hik : i = k
    · subst hik; simp
    · simp [Pi.single_eq_of_ne hik]
  conv_lhs => rw [hv]
  simp [map_sum]

theorem hol_radius {Ω : Set (Fin d → ℂ)} (hΩ : IsOpen Ω) {x₀ : Fin d → ℂ} (hx₀ : x₀ ∈ Ω) (v : Fin d → ℂ) :
    ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ Metric.closedBall x₀ R ⊆ Ω ∧
      ∀ x ∈ Metric.ball x₀ (R / 2), ∀ ζ ∈ Metric.closedBall (0 : ℂ) r, x + ζ • v ∈ Metric.closedBall x₀ R := by
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx₀)
  refine ⟨R, R / (2 * (‖v‖ + 1)), hR, by positivity, hsub, ?_⟩
  intro x hx ζ hζ
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hζ
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h1 : ‖ζ • v‖ ≤ R / 2 := by
    rw [norm_smul]
    calc ‖ζ‖ * ‖v‖ ≤ R / (2 * (‖v‖ + 1)) * (‖v‖ + 1) := by
          apply mul_le_mul hζ (by linarith) (norm_nonneg _) (by positivity)
      _ = R / 2 := by field_simp
  calc ‖x + ζ • v - x₀‖ = ‖(x - x₀) + ζ • v‖ := by congr 1; abel
    _ ≤ ‖x - x₀‖ + ‖ζ • v‖ := norm_add_le _ _
    _ ≤ R := by linarith

theorem hol_continuousOn_fderiv_apply {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (v : Fin d → ℂ) : ContinuousOn (fun x => fderiv ℂ g x v) Ω := by
  intro x₀ hx₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨R, r, hR, hr, hsub, hmem⟩ := hol_radius hΩ hx₀ v
  have hK : IsCompact (Metric.closedBall x₀ R) := isCompact_closedBall x₀ R
  have huc := hK.uniformContinuousOn_of_continuous (hg.continuousOn.mono hsub)
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε * r / 2) (by positivity)
  refine ⟨min δ (R / 2), lt_min hδ (by positivity), ?_⟩
  intro x hx
  have hx1 : dist x x₀ < δ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : x ∈ Metric.ball x₀ (R / 2) := lt_of_lt_of_le hx (min_le_right _ _)
  have hx0 : x₀ ∈ Metric.ball x₀ (R / 2) := Metric.mem_ball_self (by positivity)
  have hd : ∀ ζ ∈ Metric.closedBall (0 : ℂ) r,
      HasDerivAt (fun ζ : ℂ => g (x + ζ • v) - g (x₀ + ζ • v))
        (fderiv ℂ g (x + ζ • v) v - fderiv ℂ g (x₀ + ζ • v) v) ζ := fun ζ hζ =>
    (hol_hasDerivAt_line hΩ hg x v ζ (hsub (hmem x hx2 ζ hζ))).sub
      (hol_hasDerivAt_line hΩ hg x₀ v ζ (hsub (hmem x₀ hx0 ζ hζ)))
  have hdc : DiffContOnCl ℂ (fun ζ : ℂ => g (x + ζ • v) - g (x₀ + ζ • v)) (Metric.ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    intro ζ hζ
    exact (hd ζ (Metric.closure_ball_subset_closedBall hζ)).differentiableAt.differentiableWithinAt
  have hb : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ‖g (x + ζ • v) - g (x₀ + ζ • v)‖ ≤ ε * r / 2 := by
    intro ζ hζ
    have hζ' := Metric.sphere_subset_closedBall hζ
    rw [← dist_eq_norm]
    apply le_of_lt
    apply hδ' _ (hmem x hx2 ζ hζ') _ (hmem x₀ hx0 ζ hζ')
    simpa using hx1
  have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc hb
  have h2 := (hd 0 (Metric.mem_closedBall_self hr.le)).deriv
  rw [h2] at h1
  simp only [zero_smul, add_zero] at h1
  rw [dist_eq_norm]
  calc ‖fderiv ℂ g x v - fderiv ℂ g x₀ v‖ ≤ ε * r / 2 / r := h1
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

theorem hol_continuousOn_fderiv {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) : ContinuousOn (fderiv ℂ g) Ω := by
  have h : fderiv ℂ g = fun x => ∑ k, (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).smulRight
      (fderiv ℂ g x (Pi.single k 1)) := by
    funext x; exact hol_clm_decomp _
  rw [h]
  refine continuousOn_finsetSum _ fun k _ => ?_
  have hc : Continuous fun w : F => (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).smulRight w :=
    (ContinuousLinearMap.smulRightL ℂ (Fin d → ℂ) F (ContinuousLinearMap.proj k)).continuous
  exact hc.comp_continuousOn (hol_continuousOn_fderiv_apply hΩ hg _)

theorem hol_differentiableOn_fderiv_apply [CompleteSpace F] {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (v : Fin d → ℂ) :
    DifferentiableOn ℂ (fun x => fderiv ℂ g x v) Ω := by
  intro x₀ hx₀
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨R, r, hR, hr, hsub, hmem⟩ := hol_radius hΩ hx₀ v
  have hK : IsCompact (Metric.closedBall x₀ R) := isCompact_closedBall x₀ R
  have hcf := hol_continuousOn_fderiv hΩ hg
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcf.mono hsub)
  have hs : Metric.ball x₀ (R / 2) ∈ nhds x₀ := Metric.ball_mem_nhds x₀ (by positivity)
  have hx0 : x₀ ∈ Metric.ball x₀ (R / 2) := Metric.mem_ball_self (by positivity)
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ Metric.closedBall (0 : ℂ) r := fun θ =>
    Metric.sphere_subset_closedBall (circleMap_mem_sphere 0 hr.le θ)

  let c : ℝ → ℂ := fun θ => deriv (circleMap 0 r) θ * ((circleMap 0 r θ - 0) ^ 2)⁻¹
  have hc : Continuous c := by
    have h1 : Continuous fun θ : ℝ => deriv (circleMap 0 r) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 r).mul continuous_const
    refine h1.mul (Continuous.inv₀ (((continuous_circleMap 0 r).sub continuous_const).pow 2) ?_)
    intro θ
    have := circleMap_ne_center (c := (0 : ℂ)) (θ := θ) hr.ne'
    simpa using this
  have hp : ∀ x : Fin d → ℂ, Continuous fun θ : ℝ => x + circleMap 0 r θ • v := fun x =>
    continuous_const.add ((continuous_circleMap 0 r).smul continuous_const)
  have hFc : ∀ x ∈ Metric.ball x₀ (R / 2), Continuous fun θ : ℝ => c θ • g (x + circleMap 0 r θ • v) :=
    fun x hx => hc.smul (hg.continuousOn.comp_continuous (hp x) fun θ => hsub (hmem x hx _ (hcm θ)))
  have hF'c : Continuous fun θ : ℝ => c θ • fderiv ℂ g (x₀ + circleMap 0 r θ • v) :=
    hc.smul (hcf.comp_continuous (hp x₀) fun θ => hsub (hmem x₀ hx0 _ (hcm θ)))
  have key : HasFDerivAt (fun x => ∫ θ in (0 : ℝ)..2 * Real.pi, c θ • g (x + circleMap 0 r θ • v))
      (∫ θ in (0 : ℝ)..2 * Real.pi, c θ • fderiv ℂ g (x₀ + circleMap 0 r θ • v)) x₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (F := fun x θ => c θ • g (x + circleMap 0 r θ • v))
      (F' := fun x θ => c θ • fderiv ℂ g (x + circleMap 0 r θ • v))
      (bound := fun θ => ‖c θ‖ * M) hs ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hs] with x hx
      exact (hFc x hx).aestronglyMeasurable
    · exact (hFc x₀ hx0).intervalIntegrable _ _
    · exact hF'c.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun θ _ x hx => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM _ (hmem x hx _ (hcm θ))) (norm_nonneg _)
    · exact (hc.norm.mul continuous_const).intervalIntegrable _ _
    · refine Filter.Eventually.of_forall fun θ _ x hx => ?_
      have h1 : HasFDerivAt g (fderiv ℂ g (x + circleMap 0 r θ • v)) (x + circleMap 0 r θ • v) :=
        (hg.differentiableAt (hΩ.mem_nhds (hsub (hmem x hx _ (hcm θ))))).hasFDerivAt
      exact ((hasFDerivAt_comp_add_right (circleMap 0 r θ • v)).mpr h1).const_smul (c θ)
  have heq : (fun x => fderiv ℂ g x v) =ᶠ[nhds x₀]
      fun x => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, c θ • g (x + circleMap 0 r θ • v) := by
    filter_upwards [hs] with x hx
    have hU : IsOpen {ζ : ℂ | x + ζ • v ∈ Ω} :=
      hΩ.preimage (continuous_const.add (continuous_id.smul continuous_const))
    have hdU : DifferentiableOn ℂ (fun ζ : ℂ => g (x + ζ • v)) {ζ : ℂ | x + ζ • v ∈ Ω} := fun ζ hζ =>
      (hol_hasDerivAt_line hΩ hg x v ζ hζ).differentiableAt.differentiableWithinAt
    have h1 := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU
      (c := 0) (w₀ := 0) (R := r) (fun ζ hζ => hsub (hmem x hx ζ hζ)) hdU (Metric.mem_ball_self hr)
    have h2 := (hol_hasDerivAt_line hΩ hg x v 0 (by
      simpa using hsub (hmem x hx 0 (Metric.mem_closedBall_self hr.le)))).deriv
    simp only [zero_smul, add_zero] at h2
    rw [← h2, ← h1]
    simp only [circleIntegral, c, smul_smul]
  exact (key.const_smul _).differentiableAt.congr_of_eventuallyEq heq

theorem hol_differentiableOn_fderiv [CompleteSpace F] {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) : DifferentiableOn ℂ (fderiv ℂ g) Ω := by
  have h : fderiv ℂ g = fun x => ∑ k, (ContinuousLinearMap.proj k : (Fin d → ℂ) →L[ℂ] ℂ).smulRight
      (fderiv ℂ g x (Pi.single k 1)) := by
    funext x; exact hol_clm_decomp _
  rw [h]
  refine DifferentiableOn.fun_sum fun k _ => ?_
  exact (ContinuousLinearMap.smulRightL ℂ (Fin d → ℂ) F
    (ContinuousLinearMap.proj k)).differentiable.comp_differentiableOn
      (hol_differentiableOn_fderiv_apply hΩ hg _)

end

theorem holo_contDiffOn {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F} (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (n : ℕ) :
    ContDiffOn ℂ n g Ω := by
  induction n generalizing F with
  | zero =>
    have h0 : ContDiffOn ℂ 0 g Ω := contDiffOn_zero.2 hg.continuousOn
    simpa using h0
  | succ n ih =>
    have h : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [h, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨hg, fun h => ?_, ih (hol_differentiableOn_fderiv hΩ hg)⟩
    exact absurd h (by simp)

theorem wir_integrable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {φ : (Fin d → ℂ) → ℂ} {a : (Fin d → ℂ) → V} {Ω : Set (Fin d → ℂ)} (hΩ : IsOpen Ω) (hφ : ContinuousOn φ Ω)
    (ha : Continuous a) (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ Ω) :
    Integrable (fun x => φ x • a x) (volume : Measure (Fin d → ℂ)) := by
  have h1 : Continuous (fun x => φ x • a x) :=
    contDiff_zero.mp (contDiff_smul_of_tsupport hΩ (contDiffOn_zero.mpr hφ) (contDiff_zero.mpr ha) hsupp)
  exact h1.integrable_of_hasCompactSupport (hc.smul_left (f := φ))

theorem wir_hasLineDerivAt {d : ℕ} (β t : ℂ) {g : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ}
    (hg : DifferentiableAt ℂ g x) (v : Fin d → ℂ) :
    HasLineDerivAt ℝ (fun y => psi β (g y / t))
      (psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) x v := by
  have h0 : HasFDerivAt g ((fderiv ℂ g x).restrictScalars ℝ) x := hg.hasFDerivAt.restrictScalars ℝ
  have h1 := h0.const_mul (β / t)
  have h2 := Complex.reCLM.hasFDerivAt.comp x h1
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp x h2
  have h4 := (h3.const_mul Complex.I).cexp
  have h5 := h4.hasLineDerivAt v
  have e : (fun y => psi β (g y / t)) =
      fun y => Complex.exp (Complex.I * (Complex.ofRealCLM ∘ Complex.reCLM ∘ fun y => β / t * g y) y) := by
    funext y
    simp only [psi, Function.comp, Complex.ofRealCLM_apply, Complex.reCLM_apply]
    congr 4
    ring
  have ev : psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ)) =
      (Complex.exp (Complex.I * (Complex.ofRealCLM ∘ Complex.reCLM ∘ fun y => β / t * g y) x) •
        Complex.I • Complex.ofRealCLM ∘SL Complex.reCLM ∘SL
          ((β / t) • ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ g x))) v := by
    have := congrFun e x
    rw [this]
    simp
  rw [e, ev]
  exact h5

theorem wir_dir {d : ℕ} (β t : ℂ) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {b : (Fin d → ℂ) → V} (hb : ContDiff ℝ 1 b) (hc : HasCompactSupport b) (hsupp : tsupport b ⊆ Ω)
    (v : Fin d → ℂ) :
    Integrable (fun x => psi β (g x / t) • fderiv ℝ b x v) (volume : Measure (Fin d → ℂ)) ∧
    Integrable (fun x => (psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) • b x)
      (volume : Measure (Fin d → ℂ)) ∧
    ∫ x, psi β (g x / t) • fderiv ℝ b x v =
      -∫ x, (psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) • b x := by
  have hgc : ContinuousOn g Ω := hg.continuousOn
  have hψ : ContinuousOn (fun x => psi β (g x / t)) Ω := by
    unfold psi
    fun_prop
  have hg1 : ContDiffOn ℂ 1 g Ω := by exact_mod_cast holo_contDiffOn hΩ hg 1
  have hdg : ContinuousOn (fun x => fderiv ℂ g x v) Ω := by
    have := hg1.continuousOn_fderiv_of_isOpen hΩ le_rfl
    exact this.clm_apply continuousOn_const
  have hψ' : ContinuousOn
      (fun x => psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) Ω := by
    refine hψ.mul (continuousOn_const.mul ?_)
    exact Complex.continuous_ofReal.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hdg))
  have hdb : Continuous (fun x => fderiv ℝ b x v) :=
    (hb.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdbc : HasCompactSupport (fun x => fderiv ℝ b x v) := hc.fderiv_apply (𝕜 := ℝ) v
  have hdbs : tsupport (fun x => fderiv ℝ b x v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hsupp
  have i1 := wir_integrable hΩ hψ hdb hdbc hdbs
  have i2 := wir_integrable hΩ hψ' hb.continuous hc hsupp
  have i3 := wir_integrable hΩ hψ hb.continuous hc hsupp
  refine ⟨i1, i2, ?_⟩
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin d → ℂ))) (B := ContinuousLinearMap.lsmul ℝ ℂ)
    (f := fun x => psi β (g x / t))
    (f' := fun x => psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ)))
    (g := b) (g' := fun x => fderiv ℝ b x v) (v := v) i2 i1 i3
    (fun x hx => wir_hasLineDerivAt β t ((hg x (hsupp hx)).differentiableAt (hΩ.mem_nhds (hsupp hx))) v)
    (fun x _ => ((hb.differentiable one_ne_zero) x).hasFDerivAt.hasLineDerivAt v)
  exact key

theorem wir_lin {α V : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (F₁ F₂ : α → V) (c₁ c₂ : ℂ) (h₁ : Integrable F₁ μ) (h₂ : Integrable F₂ μ) :
    ∫ x, (c₁ • F₁ x - c₂ • F₂ x) ∂μ = c₁ • ∫ x, F₁ x ∂μ - c₂ • ∫ x, F₂ x ∂μ := by
  have h₁' : Integrable (fun x => c₁ • F₁ x) μ := h₁.smul c₁
  have h₂' : Integrable (fun x => c₂ • F₂ x) μ := h₂.smul c₂
  rw [integral_sub h₁' h₂', integral_smul, integral_smul]

theorem wirtingerIBP : WirtingerIBP := by
  intro d β t Ω g ht hΩ hg V _ _ _ b k hb hc hsupp
  obtain ⟨a1, a2, a3⟩ := wir_dir β t hΩ hg hb hc hsupp (Pi.single k 1)
  obtain ⟨c1, c2, c3⟩ := wir_dir β t hΩ hg hb hc hsupp (Pi.single k Complex.I)
  rw [muPi_eq, integral_smul_nnreal_measure, integral_smul_nnreal_measure, ← smul_neg]
  congr 1
  have e1 : ∀ x, psi β (g x / t) • wirt k b x =
      (1 / 2 : ℂ) • (psi β (g x / t) • fderiv ℝ b x (Pi.single k 1)) -
        (Complex.I / 2) • (psi β (g x / t) • fderiv ℝ b x (Pi.single k Complex.I)) := by
    intro x
    simp only [wirt, smul_sub, smul_smul]
    congr 2 <;> ring
  have hI : (Pi.single k Complex.I : Fin d → ℂ) = Complex.I • Pi.single k 1 := by
    rw [← Pi.single_smul]; simp
  have e2 : ∀ x, (Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) • b x =
      (1 / 2 : ℂ) • ((psi β (g x / t) *
          (Complex.I * (((β / t * fderiv ℂ g x (Pi.single k 1)).re : ℝ) : ℂ))) • b x) -
        (Complex.I / 2) • ((psi β (g x / t) *
          (Complex.I * (((β / t * fderiv ℂ g x (Pi.single k Complex.I)).re : ℝ) : ℂ))) • b x) := by
    intro x
    rw [smul_smul, smul_smul, ← sub_smul]
    congr 1
    rw [hI, map_smul, smul_eq_mul]
    set w : ℂ := β / t * fderiv ℂ g x (Pi.single k 1) with hw
    have h1 : β / t * (Complex.I * fderiv ℂ g x (Pi.single k 1)) = Complex.I * w := by rw [hw]; ring
    have h2 : Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) = Complex.I * w / 2 := by
      rw [hw]; field_simp
    rw [h1, h2]
    have h3 : (Complex.I * w).re = -w.im := by simp
    rw [h3]
    conv_lhs => rw [← Complex.re_add_im w]
    push_cast
    ring
  simp_rw [e1, e2]
  rw [wir_lin _ _ _ _ a1 c1, wir_lin _ _ _ _ a2 c2, a3, c3]
  simp only [smul_neg]
  abel

def Bd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (f : E → W) (s : Set E) (x : E) (n : ℕ)
    (A P : ℝ) : Prop :=
  ∀ j ≤ n, ‖iteratedFDerivWithin ℝ j f s x‖ ≤ A * P ^ j

section Gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gen_Bd_nonneg {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : E → W} {s : Set E} {x : E} {n : ℕ}
    {A P : ℝ} (bf : Bd f s x n A P) : 0 ≤ A := by
  have h := bf 0 (Nat.zero_le n)
  rw [pow_zero, mul_one] at h
  exact (norm_nonneg _).trans h

theorem Bd.smul {𝕜' V : Type*} [NormedField 𝕜'] [NormedAlgebra ℝ 𝕜'] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace 𝕜' V] [IsScalarTower ℝ 𝕜' V] {f : E → 𝕜'} {h : E → V} {s : Set E} {x : E} {n : ℕ} {A B P : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hP : 0 ≤ P) (hf : ContDiffOn ℝ n f s) (hh : ContDiffOn ℝ n h s)
    (bf : Bd f s x n A P) (bh : Bd h s x n B P) :
    Bd (fun y => f y • h y) s x n (2 ^ n * A * B) P := by
  intro j hj
  have hA : 0 ≤ A := gen_Bd_nonneg bf
  have hB : 0 ≤ B := gen_Bd_nonneg bh
  have h1 := norm_iteratedFDerivWithin_smul_le hf hh hs.uniqueDiffOn hx (n := j) (by exact_mod_cast hj)
  refine h1.trans ?_
  have h2 : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ *
      ‖iteratedFDerivWithin ℝ (j - i) h s x‖ ≤ (j.choose i : ℝ) * (A * B * P ^ j) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 := bf i (hij.trans hj)
    have e2 := bh (j - i) ((Nat.sub_le j i).trans hj)
    have e3 : P ^ j = P ^ i * P ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
    have e4 : ‖iteratedFDerivWithin ℝ i f s x‖ * ‖iteratedFDerivWithin ℝ (j - i) h s x‖ ≤
        (A * P ^ i) * (B * P ^ (j - i)) :=
      mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg hA (pow_nonneg hP _))
    calc (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ * ‖iteratedFDerivWithin ℝ (j - i) h s x‖
        = (j.choose i : ℝ) * (‖iteratedFDerivWithin ℝ i f s x‖ * ‖iteratedFDerivWithin ℝ (j - i) h s x‖) := by ring
      _ ≤ (j.choose i : ℝ) * ((A * P ^ i) * (B * P ^ (j - i))) :=
          mul_le_mul_of_nonneg_left e4 (Nat.cast_nonneg _)
      _ = (j.choose i : ℝ) * (A * B * P ^ j) := by rw [e3]; ring
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.sum_mul]
  have h3 : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  rw [h3]
  have h4 : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
  have h5 : 0 ≤ A * B * P ^ j := mul_nonneg (mul_nonneg hA hB) (pow_nonneg hP _)
  calc (2 : ℝ) ^ j * (A * B * P ^ j) ≤ 2 ^ n * (A * B * P ^ j) := mul_le_mul_of_nonneg_right h4 h5
    _ = 2 ^ n * A * B * P ^ j := by ring

theorem Bd.sum {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (u : Finset ι) {f : ι → E → W} {A : ι → ℝ}
    {s : Set E} {x : E} {n : ℕ} {P : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hf : ∀ i ∈ u, ContDiffOn ℝ n (f i) s) (bf : ∀ i ∈ u, Bd (f i) s x n (A i) P) :
    Bd (fun y => ∑ i ∈ u, f i y) s x n (∑ i ∈ u, A i) P := by
  intro j hj
  have e0 : (fun y => ∑ i ∈ u, f i y) = ∑ i ∈ u, f i := by
    funext y; rw [Finset.sum_apply]
  rw [e0, iteratedFDerivWithin_sum_apply hs.uniqueDiffOn hx
    (fun i hi => ((hf i hi).of_le (by exact_mod_cast hj)).contDiffWithinAt hx), Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => bf i hi j hj)

theorem Bd.clm {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']
    (L : W →L[ℝ] W') {f : E → W} {s : Set E} {x : E} {n : ℕ} {A P c : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (_hP : 0 ≤ P) (hf : ContDiffOn ℝ n f s) (hL : ‖L‖ ≤ c) (bf : Bd f s x n A P) :
    Bd (fun y => L (f y)) s x n (c * A) P := by
  intro j hj
  have h1 := L.norm_iteratedFDerivWithin_comp_left (hf.contDiffWithinAt hx) hs.uniqueDiffOn hx
    (n := j) (by exact_mod_cast hj)
  have h2 : ‖iteratedFDerivWithin ℝ j (fun y => L (f y)) s x‖ ≤ ‖L‖ * ‖iteratedFDerivWithin ℝ j f s x‖ := h1
  refine h2.trans ?_
  rw [mul_assoc]
  exact mul_le_mul hL (bf j hj) (norm_nonneg _) ((norm_nonneg _).trans hL)

theorem gen_norm_iter_inv_one (i : ℕ) :
    ‖iteratedFDerivWithin ℝ i (Inv.inv : ℝ → ℝ) {0}ᶜ 1‖ = (i.factorial : ℝ) := by
  rw [iteratedFDerivWithin_of_isOpen i isOpen_compl_singleton (by simp : (1 : ℝ) ∈ ({0}ᶜ : Set ℝ)),
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  simp

theorem Bd.inv {f : E → ℝ} {s : Set E} {x : E} {n : ℕ} {κ P : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hP : 0 ≤ P) (hf : ContDiffOn ℝ n f s) (hne : ∀ y ∈ s, f y ≠ 0)
    (h0 : 0 < f x) (hκ : 1 ≤ κ) (bf : Bd f s x n (κ * f x) P) :
    Bd (fun y => (f y)⁻¹) s x n ((n.factorial : ℝ) ^ 2 * κ ^ n / f x) P := by
  intro j hj
  have hjn : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  set N0 : ℝ := f x with hN0
  have hft : ContDiffOn ℝ n (N0⁻¹ • f) s := hf.const_smul N0⁻¹
  have hmaps : Set.MapsTo (N0⁻¹ • f) s ({0}ᶜ : Set ℝ) := by
    intro y hy
    simp only [Pi.smul_apply, smul_eq_mul, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact mul_ne_zero (inv_ne_zero h0.ne') (hne y hy)
  have hone : (N0⁻¹ • f) x = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ h0.ne'
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (Inv.inv : ℝ → ℝ) {0}ᶜ ((N0⁻¹ • f) x)‖ ≤ (j.factorial : ℝ) := by
    intro i hi
    rw [hone, gen_norm_iter_inv_one]
    exact_mod_cast Nat.factorial_le hi
  have hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDerivWithin ℝ i (N0⁻¹ • f) s x‖ ≤ (κ * P) ^ i := by
    intro i hi1 hi
    rw [iteratedFDerivWithin_const_smul_apply
      ((hf.of_le (by exact_mod_cast hi.trans hj)).contDiffWithinAt hx) hs.uniqueDiffOn hx, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h0)]
    have e1 := bf i (hi.trans hj)
    have e2 : N0⁻¹ * ‖iteratedFDerivWithin ℝ i f s x‖ ≤ N0⁻¹ * (κ * N0 * P ^ i) :=
      mul_le_mul_of_nonneg_left e1 (inv_pos.mpr h0).le
    have e3 : N0⁻¹ * (κ * N0 * P ^ i) = κ * P ^ i := by field_simp
    have e4 : κ ≤ κ ^ i := le_self_pow₀ hκ (by omega)
    rw [mul_pow]
    exact (e2.trans e3.le).trans (mul_le_mul_of_nonneg_right e4 (pow_nonneg hP _))
  have hcomp := norm_iteratedFDerivWithin_comp_le (contDiffOn_inv ℝ (n := n)) hft hjn
    isOpen_compl_singleton.uniqueDiffOn hs.uniqueDiffOn hmaps hx hC hD
  have hcd : ContDiffOn ℝ n ((Inv.inv : ℝ → ℝ) ∘ (N0⁻¹ • f)) s := (contDiffOn_inv ℝ (n := n)).comp hft hmaps
  have e0 : (fun y => (f y)⁻¹) = N0⁻¹ • ((Inv.inv : ℝ → ℝ) ∘ (N0⁻¹ • f)) := by
    funext y
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, mul_inv, inv_inv]
    rw [← mul_assoc, inv_mul_cancel₀ h0.ne', one_mul]
  rw [e0, iteratedFDerivWithin_const_smul_apply ((hcd.of_le hjn).contDiffWithinAt hx) hs.uniqueDiffOn hx,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h0)]
  have f1 : (j.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hj
  have f2 : κ ^ j ≤ κ ^ n := pow_le_pow_right₀ hκ hj
  have f3 : (j.factorial : ℝ) * j.factorial * (κ * P) ^ j ≤ (n.factorial : ℝ) ^ 2 * κ ^ n * P ^ j := by
    rw [mul_pow, sq, ← mul_assoc]
    have g1 : (j.factorial : ℝ) * j.factorial ≤ (n.factorial : ℝ) * n.factorial :=
      mul_le_mul f1 f1 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul g1 f2 (pow_nonneg hκ0 _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (pow_nonneg hP _)
  calc N0⁻¹ * ‖iteratedFDerivWithin ℝ j ((Inv.inv : ℝ → ℝ) ∘ (N0⁻¹ • f)) s x‖
      ≤ N0⁻¹ * ((n.factorial : ℝ) ^ 2 * κ ^ n * P ^ j) :=
        mul_le_mul_of_nonneg_left (hcomp.trans f3) (inv_pos.mpr h0).le
    _ = (n.factorial : ℝ) ^ 2 * κ ^ n / N0 * P ^ j := by field_simp

end Gen

theorem norm_iteratedFDerivWithin_real_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {s : Set E} (hs : IsOpen s) {n : ℕ}
    (hf : ContDiffOn ℂ n f s) {x : E} (hx : x ∈ s) {j : ℕ} (hj : j ≤ n) :
    ‖iteratedFDerivWithin ℝ j f s x‖ = ‖iteratedFDerivWithin ℂ j f s x‖ := by
  have h1 := (hf.ftaylorSeriesWithin hs.uniqueDiffOn).restrictScalars ℝ
  have h2 := h1.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := j) (by exact_mod_cast hj) hs.uniqueDiffOn hx
  rw [← h2]
  exact ContinuousMultilinearMap.norm_restrictScalars _

noncomputable def bk {d : ℕ} (g : (Fin d → ℂ) → ℂ) (k : Fin d) (x : Fin d → ℂ) : ℂ :=
  (∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1)))⁻¹ • (starRingEnd ℂ) (fderiv ℂ g x (Pi.single k 1))

theorem bkb_Bd_mono {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : E → W} {s : Set E} {x : E} {n : ℕ} {A A' P : ℝ} (hP : 0 ≤ P) (hA : A ≤ A') (b : Bd f s x n A P) :
    Bd f s x n A' P := fun j hj =>
  (b j hj).trans (mul_le_mul_of_nonneg_right hA (pow_nonneg hP j))

theorem bkb_norm_single {d : ℕ} (k : Fin d) : ‖(Pi.single k (1 : ℂ) : Fin d → ℂ)‖ = 1 := by
  rw [Pi.norm_single]; simp

theorem bkb_norm_le_sum {d : ℕ} (L : (Fin d → ℂ) →L[ℂ] ℂ) : ‖L‖ ≤ ∑ l, ‖L (Pi.single l 1)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = ∑ l, v l • (Pi.single l (1 : ℂ) : Fin d → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Pi.single_smul]; simp
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v l) (norm_nonneg _)

theorem bkb_sq_le {d : ℕ} (L : (Fin d → ℂ) →L[ℂ] ℂ) :
    ‖L‖ ^ 2 ≤ d * ∑ l, Complex.normSq (L (Pi.single l 1)) := by
  have h1 := bkb_norm_le_sum L
  have h2 : (∑ l, ‖L (Pi.single l 1)‖) ^ 2 ≤ ((Finset.univ : Finset (Fin d)).card : ℝ) * ∑ l, ‖L (Pi.single l 1)‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  simp only [Complex.normSq_eq_norm_sq]
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem bkb_N_pos {d : ℕ} {L : (Fin d → ℂ) →L[ℂ] ℂ} (hL : L ≠ 0) :
    0 < ∑ l, Complex.normSq (L (Pi.single l 1)) := by
  have h := bkb_sq_le L
  have h1 : 0 < ‖L‖ ^ 2 := by positivity
  by_contra hc
  have h2 : ∑ l, Complex.normSq (L (Pi.single l 1)) ≤ 0 := not_lt.mp hc
  have : (d : ℝ) * ∑ l, Complex.normSq (L (Pi.single l 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) h2
  linarith

theorem bk_sum {d : ℕ} {g : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ} (hne : fderiv ℂ g x ≠ 0) :
    ∑ k, fderiv ℂ g x (Pi.single k 1) * bk g k x = 1 := by
  have hN := bkb_N_pos hne
  unfold bk
  have : ∀ k, fderiv ℂ g x (Pi.single k 1) *
      ((∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1)))⁻¹ • (starRingEnd ℂ) (fderiv ℂ g x (Pi.single k 1))) =
      ((∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1)))⁻¹ : ℝ) *
        ((Complex.normSq (fderiv ℂ g x (Pi.single k 1)) : ℝ) : ℂ) := by
    intro k
    rw [Complex.real_smul, Complex.normSq_eq_conj_mul_self]; ring
  simp only [this]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, ← Complex.ofReal_mul, inv_mul_cancel₀ hN.ne']
  simp

theorem bkb_u_contDiffOn {d : ℕ} {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (k : Fin d) (n : ℕ) :
    ContDiffOn ℂ n (fun x => fderiv ℂ g x (Pi.single k 1)) Ω := by
  have h := holo_contDiffOn hΩ hg (n + 1)
  have h' : ContDiffOn ℂ ((n : WithTop ℕ∞) + 1) g Ω := by exact_mod_cast h
  have h2 := ((contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mp h').2.2
  exact h2.clm_apply contDiffOn_const

theorem bkb_cu_contDiffOn {d : ℕ} {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (k : Fin d) (n : ℕ) :
    ContDiffOn ℝ n (fun x => (starRingEnd ℂ) (fderiv ℂ g x (Pi.single k 1))) Ω :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn ((bkb_u_contDiffOn hΩ hg k n).restrict_scalars ℝ)

theorem bkb_nsq_eq (z : ℂ) : Complex.normSq z = Complex.reCLM ((starRingEnd ℂ) z • z) := by
  rw [smul_eq_mul, ← Complex.normSq_eq_conj_mul_self]; simp

theorem bkb_nsq_contDiffOn {d : ℕ} {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (k : Fin d) (n : ℕ) :
    ContDiffOn ℝ n (fun x => Complex.normSq (fderiv ℂ g x (Pi.single k 1))) Ω := by
  simp only [bkb_nsq_eq]
  exact Complex.reCLM.contDiff.comp_contDiffOn
    ((bkb_cu_contDiffOn hΩ hg k n).smul ((bkb_u_contDiffOn hΩ hg k n).restrict_scalars ℝ))

theorem bkb_N_contDiffOn {d : ℕ} {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (n : ℕ) :
    ContDiffOn ℝ n (fun x => ∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1))) Ω :=
  ContDiffOn.sum fun l _ => bkb_nsq_contDiffOn hΩ hg l n

theorem bk_contDiffOn {d : ℕ} {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hne : ∀ x ∈ Ω, fderiv ℂ g x ≠ 0) (k : Fin d) (n : ℕ) :
    ContDiffOn ℝ n (bk g k) Ω := by
  unfold bk
  exact ((bkb_N_contDiffOn hΩ hg n).inv fun x hx => (bkb_N_pos (hne x hx)).ne').smul (bkb_cu_contDiffOn hΩ hg k n)

theorem bkb_u_bd {d q : ℕ} {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} {P : ℝ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) {x : Fin d → ℂ} (hx : x ∈ Ω)
    (hb : ∀ j : ℕ, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℂ (j + 1) g x‖ ≤ ‖fderiv ℂ g x‖ * P ^ j) (k : Fin d) :
    Bd (fun x => fderiv ℂ g x (Pi.single k 1)) Ω x q ‖fderiv ℂ g x‖ P := by
  intro j hj
  rw [norm_iteratedFDerivWithin_real_eq hΩ (bkb_u_contDiffOn hΩ hg k q) hx hj,
    iteratedFDerivWithin_of_isOpen j hΩ hx]
  have h := holo_contDiffOn hΩ hg (q + 1)
  have h' : ContDiffOn ℂ ((q : WithTop ℕ∞) + 1) g Ω := by exact_mod_cast h
  have h2 := ((contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mp h').2.2
  have h3 := (ContinuousLinearMap.apply ℂ ℂ (Pi.single k (1 : ℂ) : Fin d → ℂ)).norm_iteratedFDeriv_comp_left
    (h2.contDiffAt (hΩ.mem_nhds hx)) (n := j) (by exact_mod_cast hj)
  have h4 : ‖ContinuousLinearMap.apply ℂ ℂ (Pi.single k (1 : ℂ) : Fin d → ℂ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
    have := T.le_opNorm (Pi.single k (1 : ℂ) : Fin d → ℂ)
    rw [bkb_norm_single, mul_one] at this
    simpa using this
  have h5 : ‖iteratedFDeriv ℂ (j + 1) g x‖ ≤ ‖fderiv ℂ g x‖ * P ^ j := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [norm_iteratedFDeriv_one]
    · exact hb j hj0 hj
  rw [norm_iteratedFDeriv_fderiv] at h3
  calc _ ≤ _ := h3
    _ ≤ 1 * ‖iteratedFDeriv ℂ (j + 1) g x‖ := mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h5

theorem bk_bound (d q : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (Ω : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ) (P : ℝ), IsOpen Ω →
    DifferentiableOn ℂ g Ω → 0 < P → (∀ x ∈ Ω, fderiv ℂ g x ≠ 0) → ∀ x ∈ Ω,
    (∀ j : ℕ, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℂ (j + 1) g x‖ ≤ ‖fderiv ℂ g x‖ * P ^ j) →
    ∀ k : Fin d, Bd (bk g k) Ω x q (B / ‖fderiv ℂ g x‖) P := by
  refine ⟨2 ^ q * ((q.factorial : ℝ) ^ 2 * ((d : ℝ) ^ 2 * 2 ^ q) ^ q) * d, by positivity, ?_⟩
  intro Ω g P hΩ hg hP hne x hx hb k
  set G := ‖fderiv ℂ g x‖ with hG
  have hGpos : 0 < G := norm_pos_iff.mpr (hne x hx)
  have hd : 1 ≤ (d : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (Fin.pos k))
  have bu := fun l => bkb_u_bd hΩ hg hx hb l
  have bcu : ∀ l, Bd (fun x => (starRingEnd ℂ) (fderiv ℂ g x (Pi.single l 1))) Ω x q (1 * G) P := fun l =>
    Bd.clm (Complex.conjCLE : ℂ →L[ℝ] ℂ) hΩ hx hP.le ((bkb_u_contDiffOn hΩ hg l q).restrict_scalars ℝ)
      Complex.conjCLE_norm.le (bu l)
  have bn : ∀ l, Bd (fun x => Complex.normSq (fderiv ℂ g x (Pi.single l 1))) Ω x q
      (1 * (2 ^ q * (1 * G) * G)) P := fun l => by
    simp only [bkb_nsq_eq]
    exact Bd.clm Complex.reCLM hΩ hx hP.le
      ((bkb_cu_contDiffOn hΩ hg l q).smul ((bkb_u_contDiffOn hΩ hg l q).restrict_scalars ℝ))
      Complex.reCLM_norm.le
      (Bd.smul hΩ hx hP.le (bkb_cu_contDiffOn hΩ hg l q) ((bkb_u_contDiffOn hΩ hg l q).restrict_scalars ℝ)
        (bcu l) (bu l))
  have bN := Bd.sum (Finset.univ : Finset (Fin d)) hΩ hx (fun l _ => bkb_nsq_contDiffOn hΩ hg l q)
    (fun l _ => bn l)
  set N0 := ∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1)) with hN0
  have hN0pos : 0 < N0 := bkb_N_pos (hne x hx)
  have hsq : G ^ 2 ≤ d * N0 := bkb_sq_le _
  have bN' : Bd (fun x => ∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1))) Ω x q
      (((d : ℝ) ^ 2 * 2 ^ q) * N0) P := by
    refine bkb_Bd_mono hP.le ?_ bN
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul]
    have : (d : ℝ) * (2 ^ q * G * G) = d * 2 ^ q * G ^ 2 := by ring
    rw [this]
    calc (d : ℝ) * 2 ^ q * G ^ 2 ≤ d * 2 ^ q * (d * N0) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  have hκ : (1 : ℝ) ≤ (d : ℝ) ^ 2 * 2 ^ q := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hd
    have h2 : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
    nlinarith
  have bI := Bd.inv hΩ hx hP.le (bkb_N_contDiffOn hΩ hg q) (fun y hy => (bkb_N_pos (hne y hy)).ne') hN0pos hκ bN'
  have bb := Bd.smul hΩ hx hP.le
    ((bkb_N_contDiffOn hΩ hg q).inv fun y hy => (bkb_N_pos (hne y hy)).ne') (bkb_cu_contDiffOn hΩ hg k q)
    bI (bcu k)
  refine bkb_Bd_mono hP.le ?_ bb
  rw [one_mul, le_div_iff₀ hGpos]
  set K := (q.factorial : ℝ) ^ 2 * ((d : ℝ) ^ 2 * 2 ^ q) ^ q with hK
  have hKnn : 0 ≤ K := by positivity
  have : 2 ^ q * (K / N0) * G * G = 2 ^ q * K * (G ^ 2 / N0) := by ring
  rw [this]
  have h3 : G ^ 2 / N0 ≤ d := by rw [div_le_iff₀ hN0pos]; exact hsq
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

section Main

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}

theorem norm_psi (β w : ℂ) : ‖psi β w‖ = 1 := by
  unfold psi
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

noncomputable def wirtL (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ} (k : Fin d) :
    ((Fin d → ℂ) →L[ℝ] V) →L[ℝ] V :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ V (Pi.single k (1 : ℂ) : Fin d → ℂ) -
    Complex.I • ContinuousLinearMap.apply ℝ V (Pi.single k Complex.I : Fin d → ℂ))

theorem wirt_eq (k : Fin d) (b : (Fin d → ℂ) → V) : wirt k b = (wirtL V k) ∘ (fderiv ℝ b) := by
  funext x
  simp [wirt, wirtL]

theorem norm_wirtL_le (k : Fin d) : ‖wirtL V k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
  have h1 : ‖T (Pi.single k (1 : ℂ))‖ ≤ ‖T‖ := by
    refine (T.le_opNorm _).trans ?_
    rw [Pi.norm_single]; simp
  have h2 : ‖T (Pi.single k Complex.I)‖ ≤ ‖T‖ := by
    refine (T.le_opNorm _).trans ?_
    rw [Pi.norm_single]; simp
  have : wirtL V k T = (1 / 2 : ℂ) • (T (Pi.single k 1) - Complex.I • T (Pi.single k Complex.I)) := by
    simp [wirtL]
  rw [this, norm_smul]
  have h3 : ‖T (Pi.single k 1) - Complex.I • T (Pi.single k Complex.I)‖ ≤ ‖T‖ + ‖T‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    exact add_le_add h1 h2
  have h4 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h4]; linarith

theorem wirt_contDiff {n : ℕ} (k : Fin d) {f : (Fin d → ℂ) → V} (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ n (wirt k f) := by
  rw [wirt_eq]
  exact (wirtL V k).contDiff.comp (hf.fderiv_right (by norm_cast))

theorem wirt_tsupport (k : Fin d) (f : (Fin d → ℂ) → V) : tsupport (wirt k f) ⊆ tsupport f := by
  refine subset_trans ?_ (tsupport_fderiv_subset ℝ (f := f))
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h; apply hx; rw [wirt_eq]; simp [h]

theorem wirt_bound {n : ℕ} (k : Fin d) {f : (Fin d → ℂ) → V} (hf : ContDiff ℝ (n + 1 : ℕ) f) {j : ℕ} (hj : j ≤ n)
    (x : Fin d → ℂ) : ‖iteratedFDeriv ℝ j (wirt k f) x‖ ≤ ‖iteratedFDeriv ℝ (j + 1) f x‖ := by
  rw [wirt_eq]
  have h1 : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by norm_cast)
  refine ((wirtL V k).norm_iteratedFDeriv_comp_left (N := n) h1.contDiffAt (by exact_mod_cast hj)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ (j + 1) f x‖ := by gcongr; exact norm_wirtL_le k
    _ = _ := one_mul _

theorem base_bound (β t : ℂ) (g : (Fin d → ℂ) → ℂ) {S : ℝ} {a : (Fin d → ℂ) → V} (hc : HasCompactSupport a)
    (hb : ∀ x, ‖a x‖ ≤ S) :
    ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d))‖ ≤ S * (muPi β (Fin d) (tsupport a)).toReal := by
  have h1 : ∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) =
      ∫ x in tsupport a, psi β (g x / t) • a x ∂(muPi β (Fin d)) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  rw [h1]
  refine norm_setIntegral_le_of_norm_le_const (IsCompact.measure_lt_top hc) ?_
  intro x _
  rw [norm_smul, norm_psi, one_mul]
  exact hb x

end Main

section Main2

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {d : ℕ}

theorem fk_bound {q n : ℕ} (hn : n ≤ q) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} {η P B S : ℝ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hη : 0 < η) (hP : 0 < P) (hlow : ∀ x ∈ Ω, η ≤ ‖fderiv ℂ g x‖) (hB : 0 ≤ B)
    (hbk : ∀ x ∈ Ω, ∀ k, Bd (bk g k) Ω x q (B / ‖fderiv ℂ g x‖) P)
    {a : (Fin d → ℂ) → V} (ha : ContDiff ℝ n a) (hsupp : tsupport a ⊆ Ω)
    (hb : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S * P ^ j) (k : Fin d) :
    ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun y => bk g k y • a y) x‖ ≤ (2 ^ q * B * S / η) * P ^ j := by
  have hS : 0 ≤ S := by
    have := hb 0 (Nat.zero_le _) 0
    simp only [pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hne : ∀ x ∈ Ω, fderiv ℂ g x ≠ 0 := fun x hx h => by
    have := hlow x hx
    rw [h, norm_zero] at this
    linarith
  intro j hj x
  by_cases hx : x ∈ Ω
  · have b1 : Bd (bk g k) Ω x n (B / ‖fderiv ℂ g x‖) P := fun i hi => hbk x hx k i (hi.trans hn)
    have b2 : Bd a Ω x n S P := fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hΩ hx]; exact hb i hi x
    have b3 := Bd.smul hΩ hx hP.le (bk_contDiffOn hΩ hg hne k n) ha.contDiffOn b1 b2 j hj
    rw [iteratedFDerivWithin_of_isOpen j hΩ hx] at b3
    refine b3.trans ?_
    have hG : 0 < ‖fderiv ℂ g x‖ := lt_of_lt_of_le hη (hlow x hx)
    have h1 : B / ‖fderiv ℂ g x‖ ≤ B / η := div_le_div_of_nonneg_left hB hη (hlow x hx)
    have h2 : (2 : ℝ) ^ n ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hn
    have h3 : 2 ^ q * B * S / η = 2 ^ q * (B / η) * S := by ring
    rw [h3]
    have h4 : 0 ≤ B / ‖fderiv ℂ g x‖ := div_nonneg hB hG.le
    gcongr
  · have hx' : x ∉ tsupport (fun y => bk g k y • a y) := fun h =>
      hx (hsupp (tsupport_smul_subset' _ _ h))
    have hx'' : x ∉ tsupport (iteratedFDeriv ℝ j (fun y => bk g k y • a y)) := fun h =>
      hx' (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) j h)
    rw [image_eq_zero_of_notMem_tsupport hx'', norm_zero]
    positivity

theorem ibp_identity {β t : ℂ} (hβ : β ≠ 0) (ht : t ≠ 0) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hne : ∀ x ∈ Ω, fderiv ℂ g x ≠ 0)
    {a : (Fin d → ℂ) → V} (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ Ω) :
    ∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) =
      ∑ k : Fin d, (-(2 * t / (Complex.I * β))) •
        ∫ x : Fin d → ℂ, psi β (g x / t) • wirt k (fun y => bk g k y • a y) x ∂(muPi β (Fin d)) := by
  have hf : ∀ k, ContDiff ℝ 1 (fun y => bk g k y • a y) := fun k =>
    contDiff_smul_of_tsupport hΩ (by exact_mod_cast bk_contDiffOn hΩ hg hne k 1) ha hsupp
  have hfs : ∀ k, tsupport (fun y => bk g k y • a y) ⊆ tsupport a := fun k => tsupport_smul_subset' _ _
  have hfc : ∀ k, HasCompactSupport (fun y => bk g k y • a y) := fun k =>
    hc.of_isClosed_subset (isClosed_tsupport _) (hfs k)
  have hW : ∀ k, ∫ x : Fin d → ℂ, psi β (g x / t) • wirt k (fun y => bk g k y • a y) x ∂(muPi β (Fin d)) =
      -∫ x : Fin d → ℂ, (Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) •
        (bk g k x • a x) ∂(muPi β (Fin d)) := fun k =>
    wirtingerIBP d β t Ω g ht hΩ hg V _ k (hf k) (hfc k) ((hfs k).trans hsupp)
  have hcont : ∀ k, ContinuousOn (fun x => Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) *
      psi β (g x / t)) Ω := by
    intro k
    have h1 : ContinuousOn (fderiv ℂ g) Ω :=
      ((holo_contDiffOn hΩ hg 1).continuousOn_fderiv_of_isOpen hΩ (by norm_num))
    have h2 : ContinuousOn (fun x => fderiv ℂ g x (Pi.single k 1)) Ω := h1.clm_apply continuousOn_const
    have h3 : ContinuousOn (fun x => psi β (g x / t)) Ω := by
      unfold psi
      refine Complex.continuous_exp.comp_continuousOn ?_
      refine continuousOn_const.mul ?_
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine Complex.continuous_re.comp_continuousOn ?_
      exact continuousOn_const.mul (hg.continuousOn.div_const _)
    exact (((continuousOn_const.mul h2).div_const _).mul h3)
  have hint : ∀ k, Integrable (fun x => (Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) *
      psi β (g x / t)) • (bk g k x • a x)) (muPi β (Fin d)) := by
    intro k
    have h1 : ContDiff ℝ 0 (fun x => (Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) *
      psi β (g x / t)) • (bk g k x • a x)) :=
      contDiff_smul_of_tsupport hΩ (contDiffOn_zero.mpr (hcont k)) ((hf k).of_le (by norm_num))
        ((hfs k).trans hsupp)
    refine (contDiff_zero.mp h1).integrable_of_hasCompactSupport ?_
    exact (hfc k).of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset' _ _)
  have hpt : ∀ x, psi β (g x / t) • a x = ∑ k : Fin d, (2 * t / (Complex.I * β)) •
      ((Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) • (bk g k x • a x)) := by
    intro x
    by_cases hx : x ∈ Ω
    · have h1 := bk_sum (hne x hx)
      have h2 : ∀ k : Fin d, (2 * t / (Complex.I * β)) •
          ((Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) • (bk g k x • a x)) =
          (fderiv ℂ g x (Pi.single k 1) * bk g k x) • (psi β (g x / t) • a x) := by
        intro k
        simp only [smul_smul]
        congr 1
        have : Complex.I ≠ 0 := Complex.I_ne_zero
        field_simp
      simp only [h2]
      rw [← Finset.sum_smul, h1, one_smul]
    · have : a x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)
      simp [this]
  simp only [hpt]
  have hint' : ∀ k ∈ (Finset.univ : Finset (Fin d)), Integrable (fun x => (2 * t / (Complex.I * β)) •
      ((Complex.I * β * fderiv ℂ g x (Pi.single k 1) / (2 * t) * psi β (g x / t)) • (bk g k x • a x)))
      (muPi β (Fin d)) := fun k _ => (hint k).smul _
  rw [integral_finsetSum _ hint']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul, hW k, neg_smul, smul_neg, neg_neg]

theorem main_induction {q : ℕ} {β t : ℂ} (hβ : β ≠ 0) (ht : t ≠ 0) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ}
    {η P B : ℝ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hη : 0 < η) (hP : 0 < P) (hlow : ∀ x ∈ Ω, η ≤ ‖fderiv ℂ g x‖) (hB : 0 ≤ B)
    (hbk : ∀ x ∈ Ω, ∀ k, Bd (bk g k) Ω x q (B / ‖fderiv ℂ g x‖) P) :
    ∀ n ≤ q, ∀ (S : ℝ) (a : (Fin d → ℂ) → V), ContDiff ℝ n a → HasCompactSupport a → tsupport a ⊆ Ω →
      (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S * P ^ j) →
      ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d))‖ ≤
        (2 / ‖β‖ * d * (2 ^ q * B)) ^ n * S * (‖t‖ * P / η) ^ n * (muPi β (Fin d) (tsupport a)).toReal := by
  have hne : ∀ x ∈ Ω, fderiv ℂ g x ≠ 0 := fun x hx h => by
    have := hlow x hx
    rw [h, norm_zero] at this
    linarith
  intro n
  induction n with
  | zero =>
    intro _ S a _ hc _ hb
    simp only [pow_zero, one_mul, mul_one]
    refine base_bound β t g hc fun x => ?_
    have := hb 0 le_rfl x
    simpa using this
  | succ n ih =>
    intro hn S a ha hc hsupp hb
    have hS : 0 ≤ S := by
      have := hb 0 (Nat.zero_le _) 0
      simp only [pow_zero, mul_one] at this
      exact (norm_nonneg _).trans this
    have hf : ∀ k, ContDiff ℝ (n + 1 : ℕ) (fun y => bk g k y • a y) := fun k =>
      contDiff_smul_of_tsupport hΩ (bk_contDiffOn hΩ hg hne k (n + 1)) ha hsupp
    have hfs : ∀ k, tsupport (fun y => bk g k y • a y) ⊆ tsupport a := fun k => tsupport_smul_subset' _ _
    have hws : ∀ k, tsupport (wirt k (fun y => bk g k y • a y)) ⊆ tsupport a := fun k =>
      (wirt_tsupport k _).trans (hfs k)
    have hfb := fun k => fk_bound hn hΩ hg hη hP hlow hB hbk ha hsupp hb k
    have hβ' : 0 < ‖β‖ := norm_pos_iff.mpr hβ
    have hk : ∀ k : Fin d, ‖∫ x : Fin d → ℂ, psi β (g x / t) • wirt k (fun y => bk g k y • a y) x
        ∂(muPi β (Fin d))‖ ≤ (2 / ‖β‖ * d * (2 ^ q * B)) ^ n * (2 ^ q * B * S / η * P) * (‖t‖ * P / η) ^ n *
          (muPi β (Fin d) (tsupport a)).toReal := by
      intro k
      have h1 := ih (Nat.le_of_succ_le hn) (2 ^ q * B * S / η * P) (wirt k (fun y => bk g k y • a y))
        (wirt_contDiff k (hf k)) (hc.of_isClosed_subset (isClosed_tsupport _) (hws k)) ((hws k).trans hsupp)
        (fun j hj x => by
          refine (wirt_bound k (hf k) hj x).trans ?_
          refine (hfb k (j + 1) (Nat.succ_le_succ hj) x).trans (le_of_eq ?_)
          ring)
      refine h1.trans ?_
      have h2 : (muPi β (Fin d) (tsupport (wirt k (fun y => bk g k y • a y)))).toReal ≤
          (muPi β (Fin d) (tsupport a)).toReal :=
        ENNReal.toReal_mono (IsCompact.measure_lt_top hc).ne (measure_mono (hws k))
      gcongr
    rw [ibp_identity hβ ht hΩ hg hne (ha.of_le (by norm_cast; omega)) hc hsupp]
    refine (norm_sum_le _ _).trans ?_
    have hc' : ‖-(2 * t / (Complex.I * β))‖ = 2 * ‖t‖ / ‖β‖ := by
      rw [norm_neg, norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul]; simp
    calc ∑ k : Fin d, ‖(-(2 * t / (Complex.I * β))) • ∫ x : Fin d → ℂ, psi β (g x / t) •
            wirt k (fun y => bk g k y • a y) x ∂(muPi β (Fin d))‖
        ≤ ∑ _k : Fin d, (2 * ‖t‖ / ‖β‖) * ((2 / ‖β‖ * d * (2 ^ q * B)) ^ n * (2 ^ q * B * S / η * P) *
            (‖t‖ * P / η) ^ n * (muPi β (Fin d) (tsupport a)).toReal) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_smul, hc']
          gcongr
          exact hk k
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

end Main2

theorem nonStatPhase : NonStatPhase := by
  intro d q β hβ
  obtain ⟨B, hB, hBk⟩ := bk_bound d q
  refine ⟨(2 / ‖β‖ * d * (2 ^ q * B)) ^ q, ?_⟩
  intro Ω g η P S hΩ hg hη hP hlow hder V _ _ _ a ha hc hsupp hb t ht
  have hne : ∀ x ∈ Ω, fderiv ℂ g x ≠ 0 := fun x hx h => by
    have := hlow x hx
    rw [h, norm_zero] at this
    linarith
  exact main_induction hβ ht hΩ hg hη hP hlow hB
    (fun x hx k => hBk Ω g P hΩ hg hP hne x hx (hder x hx) k) q le_rfl S a ha hc hsupp hb

end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts

namespace Formalism.FourierDecayAlt.P

theorem wirtinger_integration_by_parts : Formalism.FourierDecayAlt.G.WirtingerIBP := WirtingerIntegrationByParts.wirtingerIBP

theorem nonstationary_phase : Formalism.FourierDecayAlt.G.NonStatPhase := WirtingerIntegrationByParts.nonStatPhase

end Formalism.FourierDecayAlt.P
