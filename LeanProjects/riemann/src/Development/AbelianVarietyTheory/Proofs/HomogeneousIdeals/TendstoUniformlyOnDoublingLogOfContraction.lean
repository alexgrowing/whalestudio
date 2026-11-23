import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Metric Set Filter Asymptotics
open scoped Topology

namespace GlobalTheory

section Taylor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem isBigO_sub_linear_sq_of_analyticAt {f : E → F} {L : E →L[ℂ] F} (hf : AnalyticAt ℂ f 0)
    (h0 : f 0 = 0) (hL : HasFDerivAt f L 0) :
    (fun x => f x - L x) =O[𝓝 0] fun x => ‖x‖ ^ 2 := by
  obtain ⟨p, hp⟩ := hf
  have h1 := hp.isBigO_sub_partialSum_pow 2
  have h2 : L = continuousMultilinearCurryFin1 ℂ E F (p 1) := hL.unique hp.hasFDerivAt
  refine h1.congr_left fun x => ?_
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, hp.coeff_zero, h0, h2]
  congr 1
  ext i
  simp [Fin.snoc]

theorem map_zero_of_isBigO_sq {f : E → F} {L : E →L[ℂ] F}
    (h : (fun x => f x - L x) =O[𝓝 0] fun x => ‖x‖ ^ 2) : f 0 = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  simpa using hC.self_of_nhds

theorem hasFDerivAt_of_isBigO_sq {f : E → F} {L : E →L[ℂ] F}
    (h : (fun x => f x - L x) =O[𝓝 0] fun x => ‖x‖ ^ 2) : HasFDerivAt f L 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, map_zero_of_isBigO_sq h, sub_zero]
  exact h.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

end Taylor

section Halving

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def doublingLog (ε : V → V) (x : V) : V :=
  limUnder atTop fun j : ℕ => (2 : ℂ) ^ j • ε^[j] x

variable {ε : V → V} {r C : ℝ}

omit [NormedSpace ℂ V] in
theorem norm_iterate_le_of_contraction (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) : ‖ε^[j] x‖ ≤ (5 / 8) ^ j * ‖x‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (5 / 8 : ℝ) ^ j * ‖x‖ ≤ ‖x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
    have h2 : ε^[j] x ∈ ball (0 : V) r := by
      rw [mem_ball_zero_iff] at hx ⊢
      linarith
    rw [Function.iterate_succ_apply', pow_succ]
    linarith [hc _ h2]

omit [NormedSpace ℂ V] in
theorem norm_iterate_le_self_of_contraction (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) : ‖ε^[j] x‖ ≤ ‖x‖ :=
  (norm_iterate_le_of_contraction hc hx j).trans
    (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num)))

omit [NormedSpace ℂ V] in
theorem iterate_mem_ball_of_contraction (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) : ε^[j] x ∈ ball (0 : V) r :=
  mem_ball_zero_iff.mpr
    ((norm_iterate_le_self_of_contraction hc hx j).trans_lt (mem_ball_zero_iff.mp hx))

theorem dist_two_pow_smul_iterate_succ_le (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2)
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) :
    dist ((2 : ℂ) ^ j • ε^[j] x) ((2 : ℂ) ^ (j + 1) • ε^[j + 1] x)
      ≤ 2 * C * ‖x‖ ^ 2 * (25 / 32) ^ j := by
  have h1 := hC _ (iterate_mem_ball_of_contraction hc hx j)
  have h2 := norm_iterate_le_of_contraction hc hx j
  have e : (2 : ℂ) ^ (j + 1) • ε^[j + 1] x - (2 : ℂ) ^ j • ε^[j] x
      = (2 : ℂ) ^ (j + 1) • (ε (ε^[j] x) - (2 : ℂ)⁻¹ • ε^[j] x) := by
    rw [Function.iterate_succ_apply', smul_sub, smul_smul, pow_succ (2 : ℂ) j,
      mul_inv_cancel_right₀ two_ne_zero]
  rw [dist_comm, dist_eq_norm, e, norm_smul, norm_pow, Complex.norm_two]
  calc (2 : ℝ) ^ (j + 1) * ‖ε (ε^[j] x) - (2 : ℂ)⁻¹ • ε^[j] x‖
      ≤ 2 ^ (j + 1) * (C * ((5 / 8) ^ j * ‖x‖) ^ 2) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = 2 * C * ‖x‖ ^ 2 * (2 * (5 / 8) ^ 2) ^ j := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2]
        ring
    _ = _ := by norm_num

variable [CompleteSpace V]

theorem tendsto_doublingLog_of_contraction (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2)
    {x : V} (hx : x ∈ ball (0 : V) r) :
    Tendsto (fun j : ℕ => (2 : ℂ) ^ j • ε^[j] x) atTop (𝓝 (doublingLog ε x)) :=
  (cauchySeq_of_le_geometric (25 / 32) (2 * C * ‖x‖ ^ 2) (by norm_num)
    (dist_two_pow_smul_iterate_succ_le hc hC0 hC hx)).tendsto_limUnder

theorem dist_doublingLog_le_of_contraction (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2)
    {x : V} (hx : x ∈ ball (0 : V) r) (j : ℕ) :
    dist ((2 : ℂ) ^ j • ε^[j] x) (doublingLog ε x) ≤ 64 / 7 * C * ‖x‖ ^ 2 * (25 / 32) ^ j := by
  refine (dist_le_of_le_geometric_of_tendsto (25 / 32) (2 * C * ‖x‖ ^ 2) (by norm_num)
    (dist_two_pow_smul_iterate_succ_le hc hC0 hC hx)
    (tendsto_doublingLog_of_contraction hc hC0 hC hx) j).trans_eq ?_
  ring

theorem tendstoUniformlyOn_doublingLog_of_contraction
    (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2) :
    TendstoUniformlyOn (fun (j : ℕ) x => (2 : ℂ) ^ j • ε^[j] x) (doublingLog ε) atTop
      (ball 0 r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have h0 : Tendsto (fun j : ℕ => 64 / 7 * C * r ^ 2 * (25 / 32 : ℝ) ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (25 / 32 : ℝ)) (by norm_num)
      (by norm_num)).const_mul (64 / 7 * C * r ^ 2)
  filter_upwards [h0.eventually (gt_mem_nhds hη)] with j hj x hx
  rw [dist_comm]
  refine ((dist_doublingLog_le_of_contraction hc hC0 hC hx j).trans ?_).trans_lt hj
  have := (mem_ball_zero_iff.mp hx).le
  gcongr

omit [CompleteSpace V] in

theorem exists_ball_contraction
    (h : (fun x => ε x - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    ∃ r > 0, ∃ C ≥ 0, (∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖) ∧
      ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := h.exists_nonneg
  have h1 := (h.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)).bound (c := 1 / 8)
    (by norm_num)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hC.bound.and h1)
  refine ⟨r, hr, C, hC0, fun x hx => ?_, fun x hx => by simpa using (hball x hx).1⟩
  have h2 := (hball x hx).2
  have h3 : ‖(2 : ℂ)⁻¹ • x‖ = 1 / 2 * ‖x‖ := by simp [norm_smul]
  have h4 := norm_le_norm_sub_add (ε x) ((2 : ℂ)⁻¹ • x)
  linarith

theorem isBigO_doublingLog_sub
    (h : (fun x => ε x - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    (fun x => doublingLog ε x - x) =O[𝓝 0] fun x => ‖x‖ ^ 2 := by
  obtain ⟨r, hr, C, hC0, hc, hC⟩ := exists_ball_contraction h
  refine IsBigO.of_bound (64 / 7 * C) ?_
  filter_upwards [ball_mem_nhds 0 hr] with x hx
  have := dist_doublingLog_le_of_contraction hc hC0 hC hx 0
  rw [dist_comm, dist_eq_norm] at this
  simpa using this

theorem analyticAt_doublingLog [FiniteDimensional ℂ V] (ha : AnalyticAt ℂ ε 0)
    (h : (fun x => ε x - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    AnalyticAt ℂ (doublingLog ε) 0 := by
  obtain ⟨r, hr, C, hC0, hc, hC⟩ := exists_ball_contraction h
  obtain ⟨s, hs, hsa⟩ := Metric.eventually_nhds_iff_ball.mp ha.eventually_analyticAt
  have h1 : ball (0 : V) (min r s) ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  have h2 : ball (0 : V) (min r s) ⊆ ball 0 s := ball_subset_ball (min_le_right _ _)
  have hc' : ∀ x ∈ ball (0 : V) (min r s), ‖ε x‖ ≤ 5 / 8 * ‖x‖ := fun x hx => hc x (h1 hx)
  have hd : ∀ j : ℕ, DifferentiableOn ℂ ε^[j] (ball 0 (min r s)) := fun j =>
    DifferentiableOn.iterate (fun x hx => (hsa x (h2 hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => iterate_mem_ball_of_contraction hc' hx 1) j
  refine SCV.analyticAt_of_differentiableOn
    (SCV.differentiableOn_of_tendstoLocallyUniformlyOn isOpen_ball
      ((tendstoUniformlyOn_doublingLog_of_contraction hc hC0 hC).mono
        h1).tendstoLocallyUniformlyOn
      (Eventually.of_forall fun j => (hd j).const_smul _)) (ball_mem_nhds 0 (lt_min hr hs))

end Halving

section Extension

variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]

private theorem eventually_half_pow_smul_mem {s : Set V} (hs : s ∈ 𝓝 (0 : V)) (v : V) :
    ∀ᶠ j : ℕ in atTop, (2⁻¹ : ℝ) ^ j • v ∈ s := by
  have : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • v) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const v
  exact this.eventually hs

theorem addMonoidHom_eq_of_eventuallyEq {e e' : V →+ A} (h : e =ᶠ[𝓝 0] e') : e = e' := by
  ext v
  obtain ⟨j, hj⟩ := (eventually_half_pow_smul_mem h v).exists
  have hv : v = (2 ^ j : ℕ) • (2⁻¹ : ℝ) ^ j • v := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp
  rw [hv, map_nsmul, map_nsmul, show e _ = e' _ from hj]

theorem exists_addMonoidHom_eventuallyEq {g : V → A}
    (hg : ∀ᶠ p in 𝓝 (0 : V × V), g (p.1 + p.2) = g p.1 + g p.2) :
    ∃ e : V →+ A, e =ᶠ[𝓝 0] g := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hg
  have hadd : ∀ x ∈ ball (0 : V) r, ∀ y ∈ ball (0 : V) r, g (x + y) = g x + g y :=
    fun x hx y hy => hball (x, y) (by rw [← Prod.mk_zero_zero, ← ball_prod_same]; exact ⟨hx, hy⟩)
  have hhalf : ∀ x ∈ ball (0 : V) r, (2⁻¹ : ℝ) • x ∈ ball (0 : V) r := by
    intro x hx
    rw [mem_ball_zero_iff] at hx ⊢
    rw [norm_smul]
    norm_num
    linarith [norm_nonneg x]
  have hstep : ∀ x ∈ ball (0 : V) r, ∀ k : ℕ, (2⁻¹ : ℝ) ^ k • x ∈ ball (0 : V) r ∧
      (2 ^ k : ℕ) • g ((2⁻¹ : ℝ) ^ k • x) = g x := by
    intro x hx k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have h1 := hhalf _ ih.1
      rw [pow_succ' (2⁻¹ : ℝ), mul_smul]
      refine ⟨h1, ?_⟩
      rw [pow_succ, mul_smul, two_smul, ← hadd _ h1 _ h1, ← add_smul]
      norm_num
      simpa using ih.2
  have hex : ∀ v : V, ∃ j : ℕ, (2⁻¹ : ℝ) ^ j • v ∈ ball (0 : V) r := fun v =>
    (eventually_half_pow_smul_mem (ball_mem_nhds 0 hr) v).exists
  let e : V → A := fun v => (2 ^ Nat.find (hex v) : ℕ) • g ((2⁻¹ : ℝ) ^ Nat.find (hex v) • v)
  have he : ∀ (v : V) (j : ℕ), (2⁻¹ : ℝ) ^ j • v ∈ ball (0 : V) r →
      e v = (2 ^ j : ℕ) • g ((2⁻¹ : ℝ) ^ j • v) := by
    intro v j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.find_min' (hex v) hj)
    rw [pow_add, mul_smul, add_comm, pow_add, mul_smul, (hstep _ (Nat.find_spec (hex v)) k).2]
  refine ⟨AddMonoidHom.mk' e fun v w => ?_, ?_⟩
  · obtain ⟨j, h1, h2, h3⟩ := ((eventually_half_pow_smul_mem (ball_mem_nhds 0 hr) v).and
      ((eventually_half_pow_smul_mem (ball_mem_nhds 0 hr) w).and
        (eventually_half_pow_smul_mem (ball_mem_nhds 0 hr) (v + w)))).exists
    rw [he _ j h1, he _ j h2, he _ j h3, smul_add, hadd _ h1 _ h2, smul_add]
  · filter_upwards [ball_mem_nhds 0 hr] with v hv
    simpa using he v 0 (by simpa using hv)

end Extension

end GlobalTheory
