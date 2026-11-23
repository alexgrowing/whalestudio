import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandauSummableOfExpDirichletSeriesEntire
open MeasureTheory Complex Classical Filter Topology

namespace GlobalTheory

theorem genDirichlet_term_norm (a l : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ‖(a : ℂ) * Complex.exp (-(l : ℂ) * z)‖ = a * Real.exp (-l * z.re) := by
  rw [norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_of_nonneg ha]
  congr 2
  simp

theorem genDirichlet_summable_of_le {ι : Type} (a l : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hl : ∀ i, 0 ≤ l i) {y : ℝ} (hy : Summable (fun i => a i * Real.exp (-(l i) * y)))
    {z : ℂ} (hz : y ≤ z.re) :
    Summable (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) := by
  refine Summable.of_norm_bounded hy (fun i => ?_)
  rw [genDirichlet_term_norm _ _ (ha i)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i)

theorem genDirichlet_differentiableOn {ι : Type} (a l : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hl : ∀ i, 0 ≤ l i) (s : ℝ)
    (hs : ∀ y : ℝ, s < y → Summable (fun i => a i * Real.exp (-(l i) * y))) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z))
      {z : ℂ | s < z.re} := by
  intro z hz
  have hz' : s < z.re := hz
  have hU : IsOpen {w : ℂ | (s + z.re) / 2 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z))
      {w : ℂ | (s + z.re) / 2 < w.re} :=
    Complex.differentiableOn_tsum_of_summable_norm (hs ((s + z.re) / 2) (by linarith)) (fun i => by fun_prop) hU
      (fun i w hw => by
        have hw' : (s + z.re) / 2 < w.re := hw
        rw [genDirichlet_term_norm _ _ (ha i)]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i))
  exact (hD.differentiableAt (hU.mem_nhds (show (s + z.re) / 2 < z.re by linarith))).differentiableWithinAt

theorem genDirichlet_summable_pow {ι : Type} (b μ : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (hμ : ∀ j, 0 ≤ μ j)
    (t : ℝ) (h : ∀ σ : ℝ, t < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ))) (n : ℕ) (σ : ℝ)
    (hσ : t < σ) :
    Summable (fun j => b j * μ j ^ n * Real.exp (-(μ j) * σ)) := by
  set δ := (σ - t) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 := (h (σ - δ) (by rw [hδ]; linarith)).mul_left ((n.factorial : ℝ) / δ ^ n)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) h1
  · have := hb j; have := hμ j; positivity
  · have h2 := Real.pow_div_factorial_le_exp (μ j * δ) (mul_nonneg (hμ j) hδ0.le) n
    have hf : (0:ℝ) < n.factorial := by positivity
    have h3 : μ j ^ n ≤ (n.factorial : ℝ) / δ ^ n * Real.exp (μ j * δ) := by
      rw [div_le_iff₀ hf, mul_pow] at h2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have h4 : Real.exp (-(μ j) * (σ - δ)) = Real.exp (μ j * δ) * Real.exp (-(μ j) * σ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h4]
    have h5 : 0 ≤ b j * Real.exp (-(μ j) * σ) := mul_nonneg (hb j) (Real.exp_pos _).le
    calc b j * μ j ^ n * Real.exp (-(μ j) * σ) = μ j ^ n * (b j * Real.exp (-(μ j) * σ)) := by ring
      _ ≤ ((n.factorial : ℝ) / δ ^ n * Real.exp (μ j * δ)) * (b j * Real.exp (-(μ j) * σ)) :=
        mul_le_mul_of_nonneg_right h3 h5
      _ = _ := by ring

theorem genDirichlet_hasSum_iteratedDeriv {ι : Type} (b μ : ι → ℝ) (F : ℂ → ℂ)
    (hb : ∀ j, 0 ≤ b j) (hμ : ∀ j, 0 ≤ μ j) (t : ℝ)
    (h : ∀ s : ℂ, t < s.re → HasSum (fun j => (b j : ℂ) * Complex.exp (-(μ j : ℂ) * s)) (F s))
    (n : ℕ) (s : ℂ) (hs : t < s.re) :
    HasSum (fun j => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * s))
      (iteratedDeriv n F s) := by
  have hreal : ∀ σ : ℝ, t < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ)) := by
    intro σ hσ
    have := (h σ (by simpa using hσ)).summable
    rw [← Complex.summable_ofReal]
    convert this using 2
    push_cast; rfl
  induction n generalizing s with
  | zero => simpa using h s hs
  | succ n ih =>
    set σ := (t + s.re) / 2 with hσ
    have hσ1 : t < σ := by rw [hσ]; linarith
    have hσs : σ < s.re := by rw [hσ]; linarith
    have hU : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have key := Complex.hasSum_deriv_of_summable_norm
      (F := fun j w => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w))
      (U := {w : ℂ | σ < w.re}) (z := s)
      (genDirichlet_summable_pow b μ hb hμ t hreal n σ hσ1)
      (fun j => by fun_prop) hU (fun j w hw => by
        have hw' : σ < w.re := hw
        rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real,
          Complex.norm_exp, Real.norm_of_nonneg (hb j), Real.norm_of_nonneg (hμ j)]
        have h0 : 0 ≤ b j * μ j ^ n := mul_nonneg (hb j) (pow_nonneg (hμ j) n)
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h0
        have := hμ j
        simp
        nlinarith) hσs
    have hev : (fun w : ℂ => ∑' j, (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w))
        =ᶠ[nhds s] iteratedDeriv n F := by
      filter_upwards [hU.mem_nhds hσs] with w hw
      have hw' : σ < w.re := hw
      exact (ih w (by linarith)).tsum_eq
    rw [hev.deriv_eq, ← iteratedDeriv_succ] at key
    refine (congrArg (fun f => HasSum f _) (funext fun j => ?_)).mp key
    have : HasDerivAt (fun w : ℂ => (b j : ℂ) * (-(μ j : ℂ)) ^ n * Complex.exp (-(μ j : ℂ) * w))
        ((b j : ℂ) * (-(μ j : ℂ)) ^ n * (Complex.exp (-(μ j : ℂ) * s) * (-(μ j : ℂ) * 1))) s :=
      (((hasDerivAt_id s).const_mul (-(μ j : ℂ))).cexp).const_mul _
    rw [this.deriv]; ring

theorem genDirichlet_eqOn_ball_inter {F Φ : ℂ → ℂ} {T r s : ℝ} (hr : 0 < r) (hsT : s ≤ T)
    (hF : DifferentiableOn ℂ F (Metric.ball (T : ℂ) r))
    (hΦ : DifferentiableOn ℂ Φ {z : ℂ | s < z.re})
    (heq : ∀ y : ℝ, T < y → y < T + r → F y = Φ y) :
    ∀ z ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}, F z = Φ z := by
  have hU : IsOpen (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hconv : Convex ℝ (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    (convex_ball _ _).inter (convex_halfSpace_re_gt s)
  have hFa : AnalyticOnNhd ℂ F (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    (hF.mono Set.inter_subset_left).analyticOnNhd hU
  have hΦa : AnalyticOnNhd ℂ Φ (Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re}) :=
    (hΦ.mono Set.inter_subset_right).analyticOnNhd hU
  have hc : ((T + r / 2 : ℝ) : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | s < z.re} := by
    constructor
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    · show s < ((T + r / 2 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] ((T + r / 2 : ℝ) : ℂ), F z = Φ z := by
    have ht : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[>] (T + r / 2)) (𝓝[≠] ((T + r / 2 : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_inj]
        exact ne_of_gt hy
    refine ht.frequently (Eventually.frequently ?_)
    have : Set.Ioo (T + r / 2) (T + r) ∈ 𝓝[>] (T + r / 2) := Ioo_mem_nhdsGT (by linarith)
    filter_upwards [this] with y hy
    exact heq y (by linarith [hy.1]) hy.2
  exact hFa.eqOn_of_preconnected_of_frequently_eq hΦa hconv.isPreconnected hc hfreq

theorem genDirichlet_landau_step {ι : Type} (a l : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (F : ℂ → ℂ) (x₀ T : ℝ) (hT : x₀ < T) (hFa : AnalyticAt ℂ F (T : ℂ))
    (hP : ∀ y : ℝ, T < y → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y)) :
    ∃ t, x₀ ≤ t ∧ t < T ∧
      ∀ y : ℝ, t < y → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y) := by
  obtain ⟨r, hr, hFr⟩ := hFa.exists_ball_analyticOnNhd
  have hFd : DifferentiableOn ℂ F (Metric.ball (T : ℂ) r) := hFr.differentiableOn
  have hrealT : ∀ y : ℝ, T < y → Summable (fun i => a i * Real.exp (-(l i) * y)) := by
    intro y hy
    have := (hP y hy).summable
    rw [← Complex.summable_ofReal]
    convert this using 2
    push_cast; rfl
  obtain ⟨δ, hδ0, hδr, hδT⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ r / 4 ∧ δ ≤ (T - x₀) / 2 :=
    ⟨min (r / 4) ((T - x₀) / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
      min_le_right _ _⟩
  have hΦT := genDirichlet_differentiableOn a l ha hl T hrealT
  have hEq1 := genDirichlet_eqOn_ball_inter hr le_rfl hFd hΦT
    (fun y hy _ => ((hP y hy).tsum_eq).symm)
  have hU : IsOpen (Metric.ball (T : ℂ) r ∩ {z : ℂ | T < z.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hcm : ((T + δ : ℝ) : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | T < z.re} := by
    constructor
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    · show T < ((T + δ : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
  have hev : F =ᶠ[𝓝 ((T + δ : ℝ) : ℂ)]
      (fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) := by
    filter_upwards [hU.mem_nhds hcm] with z hz using hEq1 z hz
  have hΦsum : ∀ s : ℂ, T < s.re → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * s))
      ((fun z : ℂ => ∑' i, (a i : ℂ) * Complex.exp (-(l i : ℂ) * z)) s) :=
    fun s hs => (genDirichlet_summable_of_le a l ha hl (hrealT s.re hs) le_rfl).hasSum
  have hder : ∀ n : ℕ, HasSum (fun i => (a i : ℂ) * (-(l i : ℂ)) ^ n *
      Complex.exp (-(l i : ℂ) * ((T + δ : ℝ) : ℂ))) (iteratedDeriv n F ((T + δ : ℝ) : ℂ)) := by
    intro n
    rw [hev.iteratedDeriv_eq n]
    exact genDirichlet_hasSum_iteratedDeriv a l _ ha hl T hΦsum n _
      (by rw [Complex.ofReal_re]; linarith)
  have hball : Metric.ball ((T + δ : ℝ) : ℂ) (r - δ) ⊆ Metric.ball (T : ℂ) r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have hd : dist ((T + δ : ℝ) : ℂ) (T : ℂ) = δ := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        add_sub_cancel_left, abs_of_pos hδ0]
    calc dist z T ≤ dist z ((T + δ : ℝ) : ℂ) + dist ((T + δ : ℝ) : ℂ) (T : ℂ) := dist_triangle _ _ _
      _ < r := by linarith
  have hz : ((T - δ : ℝ) : ℂ) ∈ Metric.ball ((T + δ : ℝ) : ℂ) (r - δ) := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show T - δ - (T + δ) = -(2 * δ) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hTay := Complex.hasSum_re (Complex.hasSum_taylorSeries_on_ball (hFd.mono hball) hz)
  have hj : ∀ j, HasSum (fun n : ℕ => a j * Real.exp (-(l j) * (T + δ)) *
      ((2 * δ * l j) ^ n / n.factorial)) (a j * Real.exp (-(l j) * (T - δ))) := by
    intro j
    have h1 := (NormedSpace.expSeries_div_hasSum_exp (2 * δ * l j)).mul_left
      (a j * Real.exp (-(l j) * (T + δ)))
    rw [← Real.exp_eq_exp_ℝ] at h1
    have e1 : a j * Real.exp (-(l j) * (T + δ)) * Real.exp (2 * δ * l j)
        = a j * Real.exp (-(l j) * (T - δ)) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [e1] at h1
    exact h1
  have hsumT : Summable (fun i => a i * Real.exp (-(l i) * (T - δ))) := by
    refine summable_of_sum_le (fun i => mul_nonneg (ha i) (Real.exp_pos _).le)
      (c := (F ((T - δ : ℝ) : ℂ)).re) (fun S => ?_)
    refine hasSum_le (fun n => ?_) (hasSum_sum (fun j _ => hj j)) hTay
    have h2 := (hder n).mul_left ((n.factorial : ℂ)⁻¹ * (((T - δ : ℝ) : ℂ) - ((T + δ : ℝ) : ℂ)) ^ n)
    have h3 := Complex.hasSum_re h2
    have e : ∀ j, ((n.factorial : ℂ)⁻¹ * (((T - δ : ℝ) : ℂ) - ((T + δ : ℝ) : ℂ)) ^ n *
        ((a j : ℂ) * (-(l j : ℂ)) ^ n * Complex.exp (-(l j : ℂ) * ((T + δ : ℝ) : ℂ)))).re
        = a j * Real.exp (-(l j) * (T + δ)) * ((2 * δ * l j) ^ n / n.factorial) := by
      intro j
      rw [← Complex.ofReal_re (a j * Real.exp (-(l j) * (T + δ)) * ((2 * δ * l j) ^ n / n.factorial))]
      congr 1
      push_cast
      have : (2 * (δ : ℂ) * (l j : ℂ)) ^ n = ((T : ℂ) - δ - (T + δ)) ^ n * (-(l j : ℂ)) ^ n := by
        rw [← mul_pow]; congr 1; ring
      rw [this]; ring
    simp only [e] at h3
    have h4 := sum_le_hasSum S (fun j _ => by have := ha j; have := hl j; positivity) h3
    simpa only [smul_eq_mul, mul_assoc] using h4
  have hrealTd : ∀ y : ℝ, T - δ < y → Summable (fun i => a i * Real.exp (-(l i) * y)) := by
    intro y hy
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (ha i) (Real.exp_pos _).le)
      (fun i => ?_) hsumT
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hl i])) (ha i)
  have hΦTd := genDirichlet_differentiableOn a l ha hl (T - δ) hrealTd
  have hEq2 := genDirichlet_eqOn_ball_inter hr (by linarith) hFd hΦTd
    (fun y hy _ => ((hP y hy).tsum_eq).symm)
  refine ⟨T - δ, by linarith, by linarith, fun y hy => ?_⟩
  rcases lt_or_ge T y with hyT | hyT
  · exact hP y hyT
  · have hs := (genDirichlet_summable_of_le a l ha hl (hrealTd y hy)
      (show y ≤ (y : ℂ).re by rw [Complex.ofReal_re])).hasSum
    have hmem : (y : ℂ) ∈ Metric.ball (T : ℂ) r ∩ {z : ℂ | T - δ < z.re} := by
      constructor
      · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
      · show T - δ < (y : ℂ).re
        rw [Complex.ofReal_re]; exact hy
    rw [hEq2 y hmem]
    exact hs

theorem landau_hasSum_of_analyticAt (ι : Type) (a l : ι → ℝ) (x₀ x₁ : ℝ) (F : ℂ → ℂ)
    (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i) (hx : x₀ < x₁)
    (hF : ∀ x : ℝ, x₀ < x → AnalyticAt ℂ F (x : ℂ))
    (h : ∀ x : ℝ, x₁ < x → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) (F x)) :
    ∀ x : ℝ, x₀ < x → HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) (F x) := by
  let S : Set ℝ := {t | x₀ ≤ t ∧ ∀ y : ℝ, t < y →
    HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y)}
  have hne : S.Nonempty := ⟨x₁, hx.le, h⟩
  have hbdd : BddBelow S := ⟨x₀, fun t ht => ht.1⟩
  have hT0 : x₀ ≤ sInf S := le_csInf hne (fun t ht => ht.1)
  have hPT : ∀ y : ℝ, sInf S < y →
      HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * y)) (F y) := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := exists_lt_of_csInf_lt hne hy
    exact ht.2 y hty
  rcases eq_or_lt_of_le hT0 with hE | hlt
  · intro x hx0
    exact hPT x (by rw [← hE]; exact hx0)
  · obtain ⟨t, ht0, htT, hPt⟩ :=
      genDirichlet_landau_step a l ha hl F x₀ (sInf S) hlt (hF _ hlt) hPT
    exact absurd (csInf_le hbdd ⟨ht0, hPt⟩) (not_le.2 htT)

theorem landau_exp_hasSum_of_analyticAt (ι : Type) (a l : ι → ℝ) (x₀ x₁ : ℝ) (G : ℂ → ℂ)
    (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i) (hx : x₀ < x₁)
    (hG : ∀ x : ℝ, x₀ < x → AnalyticAt ℂ G (x : ℂ))
    (h : ∀ x : ℝ, x₁ < x → ∃ g : ℂ,
      HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) g ∧ G x = Complex.exp g) :
    ∀ x : ℝ, x₀ < x → ∃ g : ℂ,
      HasSum (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) g ∧ G x = Complex.exp g := by
  have alg : ∀ (x : ℂ) (p : Σ n : ℕ, Fin n → ι),
      (((∏ k, a (p.2 k)) / (p.1.factorial : ℝ) : ℝ) : ℂ) *
        Complex.exp (-((∑ k, l (p.2 k) : ℝ) : ℂ) * x)
      = (∏ k, (a (p.2 k) : ℂ) * Complex.exp (-(l (p.2 k) : ℂ) * x)) / (p.1.factorial : ℂ) := by
    intro x p
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    simp only [neg_mul]
    ring
  have key := landau_hasSum_of_analyticAt (Σ n : ℕ, Fin n → ι)
    (fun p => (∏ k, a (p.2 k)) / (p.1.factorial : ℝ)) (fun p => ∑ k, l (p.2 k)) x₀ x₁ G
    (fun p => div_nonneg (Finset.prod_nonneg fun k _ => ha _) (Nat.cast_nonneg _))
    (fun p => Finset.sum_nonneg fun k _ => hl _) hx hG (by
      intro x hx1
      obtain ⟨g, hg, hGx⟩ := h x hx1
      rw [hGx]
      convert hasSum_tuple_prod_exp _ g hg using 1
      funext p
      exact alg _ p)
  intro x hx0
  have hk := key x hx0
  have hinj : Function.Injective (fun i : ι => (⟨1, fun _ => i⟩ : Σ n : ℕ, Fin n → ι)) := by
    intro i j hij
    have := eq_of_heq (Sigma.mk.inj hij).2
    exact congrFun this 0
  have hs : Summable (fun i => (a i : ℂ) * Complex.exp (-(l i : ℂ) * x)) := by
    have := hk.summable.comp_injective hinj
    refine this.congr fun i => ?_
    simp
  refine ⟨_, hs.hasSum, ?_⟩
  refine hk.unique ?_
  convert hasSum_tuple_prod_exp _ _ hs.hasSum using 1
  funext p
  exact alg _ p

end GlobalTheory
