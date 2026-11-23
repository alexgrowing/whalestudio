import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt

noncomputable section

open MeasureTheory MvPolynomial Filter Topology

namespace PositivityTheory.Rg.Sw.FFTSteps

variable {m n : ℕ}

theorem gs_eq (c : ℝ) (x : Fin m → Fin n → ℂ) :
    gs c x = ((Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) : ℝ) : ℂ) := by
  unfold gs
  rw [Complex.ofReal_exp, Complex.ofReal_neg]

theorem continuous_gs (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  simp_rw [gs_eq]
  fun_prop

theorem norm_gs (c : ℝ) (x : Fin m → Fin n → ℂ) :
    ‖gs c x‖ = Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) := by
  rw [gs_eq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem gs_half (c : ℝ) (x : Fin m → Fin n → ℂ) : gs c x = gs (c / 2) x * gs (c / 2) x := by
  simp only [gs, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrable_gauss1 {c : ℝ} (hc : 0 < c) : Integrable (fun z : ℂ => Real.exp (-(c * ‖z‖ ^ 2))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (c : ℂ)) (by simpa using hc) 0 0
  refine h.norm.congr (ae_of_all _ fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  norm_cast
  rw [neg_mul]

theorem exp_sum_sum (c : ℝ) (x : Fin m → Fin n → ℂ) :
    Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) = ∏ a, ∏ i, Real.exp (-(c * ‖x a i‖ ^ 2)) := by
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem integrable_gs_row {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : Fin n → ℂ => ∏ i, Real.exp (-(c * ‖y i‖ ^ 2))) := by
  exact Integrable.fintype_prod (f := fun _ z => Real.exp (-(c * ‖z‖ ^ 2))) (fun _ => integrable_gauss1 hc)

set_option maxHeartbeats 1000000 in
theorem integrable_gs_prod {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, Real.exp (-(c * ‖x a i‖ ^ 2))) := by
  have h := Integrable.fintype_prod (ι := Fin m) (E := Fin n → ℂ) (μ := fun _ => (volume : Measure (Fin n → ℂ)))
    (f := fun _ y => ∏ i, Real.exp (-(c * ‖y i‖ ^ 2))) (fun _ => integrable_gs_row hc)
  exact h

theorem integrable_gs_re {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2))) := by
  exact (integrable_gs_prod hc).congr (ae_of_all _ fun x => (exp_sum_sum c x).symm)

theorem integrable_gs {c : ℝ} (hc : 0 < c) : Integrable (fun x : Fin m → Fin n → ℂ => gs c x) := by
  exact (integrable_gs_re hc).ofReal.congr (ae_of_all _ fun x => (gs_eq c x).symm)

theorem bound_aux {a r S : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hS : r ^ 2 ≤ S) :
    r * Real.exp (-(a * S)) ≤ 1 + 1 / a := by
  have hS0 : 0 ≤ S := le_trans (sq_nonneg r) hS
  have h1 : 1 + a * S ≤ Real.exp (a * S) := by
    have := Real.add_one_le_exp (a * S)
    linarith
  have hinv : 0 ≤ 1 / a := by positivity
  have haS : 0 ≤ a * S := mul_nonneg ha.le hS0
  have hprod : (1 + 1 / a) * (1 + a * S) = 1 + a * S + 1 / a + S := by
    field_simp
    ring
  have h2 : r ≤ (1 + 1 / a) * (1 + a * S) := by
    rw [hprod]
    nlinarith [sq_nonneg (r - 1)]
  have h3 : r ≤ (1 + 1 / a) * Real.exp (a * S) := by
    have : 0 ≤ 1 + 1 / a := by positivity
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact h3

theorem sq_le_sum_sum (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    ‖x a i‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 := by
  have h1 : ‖x a i‖ ^ 2 ≤ ∑ j, ‖x a j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ j, ‖x a j‖ ^ 2 ≤ ∑ b, ∑ j, ‖x b j‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ∑ j, ‖x b j‖ ^ 2)
      (fun b _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ a)
  exact h1.trans h2

theorem integrable_evX_gs (P : PX m n) : ∀ {c : ℝ}, 0 < c → Integrable (fun x => evX P x * gs c x) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro c hc
    have e : (fun x => evX (C a : PX m n) x * gs c x) = fun x => a * gs c x := by
      funext x
      simp [evX]
    rw [e]
    exact (integrable_gs hc).const_mul a
  | add p q hp hq =>
    intro c hc
    have e : (fun x => evX (p + q) x * gs c x) = fun x => evX p x * gs c x + evX q x * gs c x := by
      funext x
      simp only [evX, map_add, add_mul]
    rw [e]
    exact (hp hc).add (hq hc)
  | mul_X p k hp =>
    intro c hc
    have hc2 : 0 < c / 2 := by positivity
    have e : (fun x => evX (p * X k) x * gs c x) = fun x =>
        ((if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1) * gs (c / 2) x) *
          (evX p x * gs (c / 2) x) := by
      funext x
      simp only [evX, map_mul, eval_X]
      rw [gs_half c x]
      ring
    rw [e]
    refine (hp hc2).bdd_mul (c := 1 + 1 / (c / 2)) ?_ ?_
    · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ (continuous_gs _))
      by_cases hk : k.2.2 = true
      · simp only [hk, if_true]
        fun_prop
      · simp only [hk, Bool.false_eq_true, if_false]
        fun_prop
    · refine ae_of_all _ fun x => ?_
      have hn : ‖(if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1)‖ = ‖x k.1 k.2.1‖ := by
        split_ifs <;> simp
      rw [norm_mul, norm_gs, hn]
      exact bound_aux hc2 (norm_nonneg _) (sq_le_sum_sum x k.1 k.2.1)

theorem mom_add {c : ℝ} (hc : 0 < c) (R1 R2 P : PX m n) :
    mom c ((R1 + R2) * P) = mom c (R1 * P) + mom c (R2 * P) := by
  unfold mom
  have h : ∀ x, evX ((R1 + R2) * P) x * gs c x = evX (R1 * P) x * gs c x + evX (R2 * P) x * gs c x := by
    intro x
    simp only [evX, add_mul, map_add]
  simp_rw [h]
  exact integral_add (integrable_evX_gs _ hc) (integrable_evX_gs _ hc)

theorem mom_smul (c : ℝ) (a : ℂ) (R P : PX m n) : mom c ((a • R) * P) = a * mom c (R * P) := by
  unfold mom
  have h : ∀ x, evX ((a • R) * P) x * gs c x = a * (evX (R * P) x * gs c x) := by
    intro x
    simp only [evX, smul_eq_C_mul, map_mul, eval_C]
    ring
  simp_rw [h]
  exact integral_const_mul a _

theorem mom_zero (c : ℝ) (P : PX m n) : mom c (0 * P) = 0 := by
  simp [mom, evX]

theorem evX_ell (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) x = (b * gramX ε x).trace := by
  simp only [evX, map_sum, map_mul, MvPolynomial.eval_C, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX]

theorem ell_mem (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ∈
      Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n)) := by
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ ?_
  · exact Subalgebra.algebraMap_mem _ (b i j)
  · exact Algebra.subset_adjoin ⟨(j, i), rfl⟩

theorem mom_ellpow (ε : Fin m → Bool) (c : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (P : PX m n) :
    mom c ((∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k * P) =
      ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x * ((b * gramX ε x).trace) ^ k := by
  unfold mom
  congr 1
  ext x
  have e : evX ((∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k * P) x =
      (evX (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) x) ^ k * evX P x := by
    simp only [evX, map_mul, map_pow]
  rw [e, evX_ell]
  ring

theorem strip_open (δ : ℝ) : IsOpen {z : ℂ | |z.im| < δ} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem strip_conn (δ : ℝ) : IsPreconnected {z : ℂ | |z.im| < δ} := by
  have e : {z : ℂ | |z.im| < δ} = Complex.imLm ⁻¹' Set.Ioo (-δ) δ := by
    ext z; simp [abs_lt]
  rw [e]
  exact ((convex_Ioo (-δ) δ).linear_preimage Complex.imLm).isPreconnected

theorem nullIff_of (hS : SecLine) (hP : PowSpan) : NullIff := by
  intro m n ε c t hc ht P
  constructor
  · intro hN b hb
    obtain ⟨δ, hδ, hd, hre, hder⟩ := hS m n ε c t hc P b hb
    set F : ℂ → ℂ := fun z => ∫ x : Fin m → Fin n → ℂ,
      evX P x * gs c x * Complex.exp (Complex.I * ↑t * z * (b * gramX ε x).trace) with hF
    have hball : Metric.ball (0:ℂ) δ ⊆ {z : ℂ | |z.im| < δ} := by
      intro z hz
      simp only [Metric.mem_ball, dist_zero_right] at hz
      exact lt_of_le_of_lt (Complex.abs_im_le_norm z) hz
    have hzero : ∀ k, iteratedDeriv k F 0 = 0 := by
      intro k
      rw [hder k, ← mom_ellpow, hN _ (Subalgebra.pow_mem _ (ell_mem ε b) k), mul_zero]
    have hloc : F =ᶠ[𝓝 0] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0:ℂ) hδ] with z hz
      rw [← Complex.taylorSeries_eq_on_ball' hz (hd.mono hball)]
      simp [hzero]
    have han : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ} := hd.analyticOnNhd (strip_open δ)
    have h0 : (0:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
    have h1 : (1:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
    have hF1 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (strip_conn δ) h0 hloc h1
    have e1 := hre 1 (by simp)
    rw [one_smul] at e1
    rw [← e1]
    exact hF1
  · intro hall R hR
    have hR' : R ∈ Submodule.span ℂ {R : PX m n | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ),
        b.IsHermitian ∧ R = (∑ i : Fin n, ∑ j : Fin n, C (b i j) * Qp ε j i) ^ k} := by
      rw [← hP m n ε]
      exact hR
    clear hR
    induction hR' using Submodule.span_induction with
    | mem R hmem =>
      obtain ⟨b, k, hb, rfl⟩ := hmem
      obtain ⟨δ, hδ, hd, hre, hder⟩ := hS m n ε c t hc P b hb
      set F : ℂ → ℂ := fun z => ∫ x : Fin m → Fin n → ℂ,
        evX P x * gs c x * Complex.exp (Complex.I * ↑t * z * (b * gramX ε x).trace) with hF
      have han : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ} := hd.analyticOnNhd (strip_open δ)
      have h0 : (0:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
      have hreal : ∀ r : ℝ, F r = 0 := by
        intro r
        rw [show F r = _ from hre (r:ℂ) (Complex.ofReal_im r)]
        apply hall
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_smul, hb.eq, Complex.star_def, Complex.conj_ofReal]
      have hfreq : ∃ᶠ z in 𝓝[≠] (0:ℂ), F z = 0 := by
        have hc0 : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 0) (𝓝 0) := by
          simpa using Complex.continuous_ofReal.tendsto (0:ℝ)
        have hT : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (hc0.mono_left nhdsWithin_le_nhds) ?_
          filter_upwards [self_mem_nhdsWithin] with r hr
          simpa using hr
        exact hT.frequently (Frequently.of_forall hreal)
      have hloc := ((han 0 h0).frequently_zero_iff_eventually_zero).mp hfreq
      have hk := hder k
      rw [Filter.EventuallyEq.iteratedDeriv_eq k (hloc : F =ᶠ[𝓝 0] 0)] at hk
      simp at hk
      rw [mom_ellpow]
      exact hk.resolve_left (fun h => ht h.1)
    | zero => exact mom_zero c P
    | add x y _ _ hx hy => rw [mom_add hc, hx, hy, add_zero]
    | smul a x _ hx => rw [mom_smul, hx, mul_zero]

end PositivityTheory.Rg.Sw.FFTSteps
