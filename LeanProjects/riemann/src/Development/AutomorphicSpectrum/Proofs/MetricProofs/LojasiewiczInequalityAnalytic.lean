import Mathlib

open Filter Topology Metric

noncomputable section
namespace GlobalTheory.CompanionTheory.Loj

theorem one_variable {f g : ℂ → ℂ} {ρ m M : ℝ} {d : ℕ} (hρ : 0 < ρ) (hm : 0 < m)
    (hf : ∀ z ∈ closedBall (0 : ℂ) ρ, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ closedBall (0 : ℂ) ρ, AnalyticAt ℂ g z)
    (hgm : ∀ z ∈ sphere (0 : ℂ) ρ, m ≤ ‖g z‖) (hfM : ∀ z ∈ sphere (0 : ℂ) ρ, ‖f z‖ ≤ M)
    (hz : ∀ z ∈ closedBall (0 : ℂ) ρ, g z = 0 → f z = 0 ∧ analyticOrderAt g z ≤ d) :
    ‖f 0‖ ^ (d + 1) ≤ M ^ (d + 1) / m * ‖g 0‖ := by
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ := by simp [hρ.le]
  have hQ : ∀ z ∈ closedBall (0 : ℂ) ρ, AnalyticAt ℂ (fun w => f w ^ (d + 1) / g w) z := by
    intro z hzm
    by_cases h0 : g z = 0
    · obtain ⟨hf0, hord⟩ := hz z hzm h0
      have hne : analyticOrderAt g z ≠ ⊤ := ne_top_of_le_ne_top (by simp) hord
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
      have hkd : k ≤ d := by
        rw [← hk] at hord
        exact_mod_cast hord
      obtain ⟨h, hh, hh0, eh⟩ := (hg z hzm).analyticOrderAt_eq_natCast.1 hk.symm
      obtain ⟨u, hu, eu⟩ := (natCast_le_analyticOrderAt (hf z hzm) (n := 1)).1
        ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf z hzm)).2 (fun i hi => by
          obtain rfl : i = 0 := by omega
          simpa using hf0))
      obtain ⟨n, hn⟩ : ∃ n, d + 1 = (n + 1) + k := ⟨d - k, by omega⟩
      have ha : AnalyticAt ℂ (fun w => (w - z) ^ (n + 1) * (u w ^ (d + 1) / h w)) z := by
        have h1 : AnalyticAt ℂ (fun w => u w ^ (d + 1) / h w) z := (hu.fun_pow _).fun_div hh hh0
        have h2 : AnalyticAt ℂ (fun w : ℂ => (w - z) ^ (n + 1)) z := by fun_prop
        exact h2.fun_mul h1
      refine ha.congr ?_
      filter_upwards [eh, eu, hh.continuousAt.eventually_ne hh0] with w e1 e2 e3
      by_cases hw : w = z
      · subst hw
        simp [h0]
      · have hwz : w - z ≠ 0 := sub_ne_zero.2 hw
        rw [e1, e2, smul_eq_mul, smul_eq_mul, pow_one, mul_pow, hn]
        field_simp
        ring
    · exact ((hf z hzm).fun_pow _).fun_div (hg z hzm) h0
  have hdiff : DiffContOnCl ℂ (fun w => f w ^ (d + 1) / g w) (ball (0 : ℂ) ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hρ.ne']
    exact fun z hzm => (hQ z hzm).differentiableAt.differentiableWithinAt
  have hbd : ∀ z ∈ frontier (ball (0 : ℂ) ρ), ‖f z ^ (d + 1) / g z‖ ≤ M ^ (d + 1) / m := by
    intro z hzm
    rw [frontier_ball _ hρ.ne'] at hzm
    rw [norm_div, norm_pow]
    have hM : 0 ≤ M := (norm_nonneg _).trans (hfM z hzm)
    exact div_le_div₀ (pow_nonneg hM _) (pow_le_pow_left₀ (norm_nonneg _) (hfM z hzm) _) hm
      (hgm z hzm)
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff hbd
    (subset_closure (mem_ball_self hρ))
  by_cases h0 : g 0 = 0
  · simp [(hz 0 h0mem h0).1, h0]
  · have hpos : 0 < ‖g 0‖ := norm_pos_iff.2 h0
    rw [norm_div, norm_pow, div_le_iff₀ hpos] at hmax
    exact hmax

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def dirDeriv (v : E) (h : E → ℂ) : E → ℂ := fun y => fderiv ℂ h y v

theorem analyticAt_dirDeriv (v : E) {h : E → ℂ} {y : E} (hh : AnalyticAt ℂ h y) :
    AnalyticAt ℂ (dirDeriv v h) y :=
  ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hh.fderiv

theorem analyticAt_iterate_dirDeriv (v : E) {h : E → ℂ} {y : E} (hh : AnalyticAt ℂ h y) (k : ℕ) :
    AnalyticAt ℂ ((dirDeriv v)^[k] h) y := by
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact analyticAt_dirDeriv v ih

theorem continuous_line (y v : E) : Continuous (fun ζ : ℂ => y + ζ • v) := by fun_prop

theorem analyticAt_line (y v : E) (z : ℂ) : AnalyticAt ℂ (fun ζ : ℂ => y + ζ • v) z := by
  fun_prop

theorem iteratedDeriv_line {U : Set E} (hU : IsOpen U) {g : E → ℂ}
    (hg : ∀ y ∈ U, AnalyticAt ℂ g y) (y v : E) (k : ℕ) :
    ∀ z : ℂ, y + z • v ∈ U →
      iteratedDeriv k (fun ζ : ℂ => g (y + ζ • v)) z = ((dirDeriv v)^[k] g) (y + z • v) := by
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
    intro z hz
    have hev : ∀ᶠ ζ in 𝓝 z, y + ζ • v ∈ U :=
      (continuous_line y v).continuousAt.eventually_mem (hU.mem_nhds hz)
    have e : iteratedDeriv k (fun ζ : ℂ => g (y + ζ • v)) =ᶠ[𝓝 z]
        fun ζ => ((dirDeriv v)^[k] g) (y + ζ • v) := by
      filter_upwards [hev] with ζ hζ using ih ζ hζ
    rw [iteratedDeriv_succ, e.deriv_eq, Function.iterate_succ_apply']
    have hd : HasFDerivAt ((dirDeriv v)^[k] g) (fderiv ℂ ((dirDeriv v)^[k] g) (y + z • v))
        (y + z • v) := (analyticAt_iterate_dirDeriv v (hg _ hz) k).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun ζ : ℂ => y + ζ • v) v z := by
      simpa using ((hasDerivAt_id z).smul_const v).const_add y
    exact (hd.comp_hasDerivAt z hl).deriv

theorem order_le_of_iteratedDeriv_ne {h : ℂ → ℂ} {z : ℂ} (hh : AnalyticAt ℂ h z) {d : ℕ}
    (hd : iteratedDeriv d h z ≠ 0) : analyticOrderAt h z ≤ d := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : ((d + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt h z := by
    simpa using Order.add_one_le_of_lt hlt
  exact hd ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hh).1 h1 d (Nat.lt_succ_self d))

theorem lojasiewicz (e : ℕ) (f g : (Fin e → ℂ) → ℂ) (x : Fin e → ℂ) (hf : AnalyticAt ℂ f x)
    (hg : AnalyticAt ℂ g x) (hfg : ∀ᶠ y in 𝓝 x, g y = 0 → f y = 0) :
    ∃ (N : ℕ) (C : ℝ), 0 < N ∧ ∀ᶠ y in 𝓝 x, ‖f y‖ ^ N ≤ C * ‖g y‖ := by
  by_cases hz : ∀ᶠ y in 𝓝 x, g y = 0
  · refine ⟨1, 0, one_pos, ?_⟩
    filter_upwards [hz, hfg] with y h1 h2
    simp [h2 h1]
  obtain ⟨r₀, hr₀, han⟩ := Metric.eventually_nhds_iff_ball.1
    (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  obtain ⟨y₁, hy₁, hgy₁⟩ : ∃ y₁ ∈ ball x r₀, g y₁ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hz (by filter_upwards [ball_mem_nhds x hr₀] with y hy using hcon y hy)
  set v := y₁ - x with hv
  have hvr : ‖v‖ < r₀ := by simpa [hv, dist_eq_norm] using hy₁
  set φ : ℂ → ℂ := fun ζ => g (x + ζ • v) with hφ
  have hgU : ∀ y ∈ ball x r₀, AnalyticAt ℂ g y := fun y hy => (han y hy).2
  have hφa : ∀ ζ : ℂ, x + ζ • v ∈ ball x r₀ → AnalyticAt ℂ φ ζ := fun ζ hζ =>
    AnalyticAt.comp (g := g) (f := fun ζ : ℂ => x + ζ • v) (hgU _ hζ) (analyticAt_line x v ζ)
  have hunit : ∀ ζ ∈ closedBall (0 : ℂ) 1, x + ζ • v ∈ ball x r₀ := by
    intro ζ hζ
    have h1 : ‖ζ‖ ≤ 1 := by simpa using hζ
    have h2 : ‖ζ • v‖ ≤ ‖v‖ := by
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) h1
    simpa [dist_eq_norm] using lt_of_le_of_lt h2 hvr
  have hφ0 : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), φ ζ ≠ 0 := by
    refine ((hφa 0 (hunit 0 (by simp))).eventually_eq_zero_or_eventually_ne_zero).resolve_left ?_
    intro hev
    have hA : AnalyticOnNhd ℂ φ (closedBall (0 : ℂ) 1) := fun ζ hζ => hφa ζ (hunit ζ hζ)
    have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall (0 : ℂ) 1).isPreconnected (z₀ := 0) (by simp) hev
      (show (1 : ℂ) ∈ closedBall (0 : ℂ) 1 by simp)
    apply hgy₁
    simpa [hφ, hv] using this
  obtain ⟨i, hi⟩ : ∃ i, iteratedDeriv i φ 0 ≠ 0 := by
    have hφ00 := hφa 0 (hunit 0 (by simp))
    have hne : analyticOrderAt φ 0 ≠ ⊤ := by
      intro htop
      have h' := (analyticOrderAt_eq_top.1 htop).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
      obtain ⟨z, hz1, hz2⟩ := (hφ0.and h').exists
      exact hz1 hz2
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hne
    by_contra hcon
    push_neg at hcon
    have := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := d + 1) hφ00).2
      (fun j _ => hcon j)
    rw [← hd] at this
    have h2 : d + 1 ≤ d := by exact_mod_cast this
    omega
  set G := (dirDeriv v)^[i] g with hG
  have hGx : G x ≠ 0 := by
    have := iteratedDeriv_line isOpen_ball hgU x v i 0 (hunit 0 (by simp))
    rw [show (fun ζ : ℂ => g (x + ζ • v)) = φ from rfl] at this
    simpa [this] using hi
  have hGc : ContinuousAt G x :=
    (analyticAt_iterate_dirDeriv v hg i).continuousAt
  set M := ‖f x‖ + 1 with hM
  have hfb : ∀ᶠ y in 𝓝 x, ‖f y‖ ≤ M :=
    (hf.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun y hy => le_of_lt hy
  obtain ⟨r, hr, hP⟩ := Metric.eventually_nhds_iff_ball.1
    (((hfg.and (hGc.eventually_ne hGx)).and hfb).and (ball_mem_nhds x hr₀))
  obtain ⟨ε, hε, hφε⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_nhdsWithin_iff.1 hφ0)
  set ρ := min (ε / 2) (r / (2 * (‖v‖ + 1))) with hρdef
  have hv1 : 0 < ‖v‖ + 1 := by positivity
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρε : ρ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρv : ρ * ‖v‖ < r / 2 := by
    have h1 : ρ * (‖v‖ + 1) ≤ r / 2 := by
      have h2 : ρ ≤ r / (2 * (‖v‖ + 1)) := min_le_right _ _
      calc ρ * (‖v‖ + 1) ≤ r / (2 * (‖v‖ + 1)) * (‖v‖ + 1) :=
            mul_le_mul_of_nonneg_right h2 hv1.le
        _ = r / 2 := by field_simp
    nlinarith
  have hclose : ∀ y ∈ ball x (r / 2), ∀ ζ ∈ closedBall (0 : ℂ) ρ, y + ζ • v ∈ ball x r := by
    intro y hy ζ hζ
    have h1 : ‖ζ‖ ≤ ρ := by simpa using hζ
    have h2 : ‖ζ • v‖ ≤ ρ * ‖v‖ := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h3 : ‖y - x‖ < r / 2 := by simpa [dist_eq_norm] using hy
    rw [mem_ball, dist_eq_norm]
    calc ‖y + ζ • v - x‖ = ‖(y - x) + ζ • v‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖ζ • v‖ := norm_add_le _ _
      _ < r := by linarith
  have hxr : x ∈ ball x (r / 2) := mem_ball_self (by positivity)
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) ρ, ζ ∈ closedBall (0 : ℂ) ρ := fun ζ hζ => sphere_subset_closedBall hζ
  have hcont : ContinuousOn (fun ζ => ‖φ ζ‖) (sphere (0 : ℂ) ρ) := by
    intro ζ hζ
    have h1 := (hP _ (hclose x hxr ζ (hsph ζ hζ))).2
    exact (hφa ζ h1).continuousAt.norm.continuousWithinAt
  have hne : (sphere (0 : ℂ) ρ).Nonempty := NormedSpace.sphere_nonempty.2 hρ.le
  obtain ⟨ζ₀, hζ₀, hmin⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_isMinOn hne hcont
  have hφpos : ∀ ζ ∈ sphere (0 : ℂ) ρ, φ ζ ≠ 0 := by
    intro ζ hζ
    have h1 : ‖ζ‖ = ρ := by simpa using hζ
    refine hφε ζ (by simp [h1, hρε]) ?_
    intro h0
    have h00 : ζ = 0 := by simpa using h0
    rw [h00, norm_zero] at h1
    exact hρ.ne h1
  set m := ‖φ ζ₀‖ / 2 with hmdef
  have hm : 0 < m := by
    have := norm_pos_iff.2 (hφpos ζ₀ hζ₀)
    positivity
  have htube : ∀ᶠ y in 𝓝 x, ∀ ζ ∈ sphere (0 : ℂ) ρ, m < ‖g (y + ζ • v)‖ := by
    refine (isCompact_sphere (0 : ℂ) ρ).eventually_forall_of_forall_eventually fun ζ hζ => ?_
    have h1 : x + ζ • v ∈ ball x r₀ := (hP _ (hclose x hxr ζ (hsph ζ hζ))).2
    have hc : ContinuousAt (fun p : (Fin e → ℂ) × ℂ => ‖g (p.1 + p.2 • v)‖) (x, ζ) := by
      have h2 : ContinuousAt (fun p : (Fin e → ℂ) × ℂ => p.1 + p.2 • v) (x, ζ) := by fun_prop
      exact (ContinuousAt.comp (g := g) (f := fun p : (Fin e → ℂ) × ℂ => p.1 + p.2 • v)
        (x := (x, ζ)) (hgU _ h1).continuousAt h2).norm
    have hlt : m < ‖g (x + ζ • v)‖ := by
      have h3 : ‖φ ζ₀‖ ≤ ‖φ ζ‖ := hmin hζ
      have h4 : 0 < ‖φ ζ₀‖ := norm_pos_iff.2 (hφpos ζ₀ hζ₀)
      have h5 : ‖φ ζ‖ = ‖g (x + ζ • v)‖ := rfl
      rw [hmdef]
      linarith
    exact hc.eventually (lt_mem_nhds hlt)
  refine ⟨i + 1, M ^ (i + 1) / m, Nat.succ_pos i, ?_⟩
  filter_upwards [htube, ball_mem_nhds x (half_pos hr)] with y ht hy
  have hin := hclose y hy
  have key := one_variable (f := fun ζ : ℂ => f (y + ζ • v)) (g := fun ζ : ℂ => g (y + ζ • v))
    (ρ := ρ) (m := m) (M := M) (d := i) hρ hm
    (fun z hzm => AnalyticAt.comp (g := f) (f := fun ζ : ℂ => y + ζ • v)
      (han _ (hP _ (hin z hzm)).2).1 (analyticAt_line y v z))
    (fun z hzm => AnalyticAt.comp (g := g) (f := fun ζ : ℂ => y + ζ • v)
      (han _ (hP _ (hin z hzm)).2).2 (analyticAt_line y v z))
    (fun z hzm => (ht z hzm).le)
    (fun z hzm => (hP _ (hin z (hsph z hzm))).1.2)
    (fun z hzm h0 => by
      have hQ := hP _ (hin z hzm)
      refine ⟨hQ.1.1.1 h0, order_le_of_iteratedDeriv_ne
        (AnalyticAt.comp (g := g) (f := fun ζ : ℂ => y + ζ • v)
          (han _ hQ.2).2 (analyticAt_line y v z)) ?_⟩
      show iteratedDeriv i (fun ζ : ℂ => g (y + ζ • v)) z ≠ 0
      rw [iteratedDeriv_line isOpen_ball hgU y v i z hQ.2]
      exact hQ.1.1.2)
  simpa using key

end GlobalTheory.CompanionTheory.Loj
