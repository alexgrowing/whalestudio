import Mathlib

open Filter Topology

namespace GlobalTheory

theorem norm_fderiv_le_of_small_of_lipschitz {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : V → E} (hg : Differentiable ℝ g) {C δ t : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t)
    (hL : ∀ a b, ‖fderiv ℝ g a - fderiv ℝ g b‖ ≤ C * ‖a - b‖) (hδ : ∀ w, ‖g w‖ ≤ δ) (v : V) :
    ‖fderiv ℝ g v‖ ≤ 2 * δ / t + C * t := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  have key : ∀ h : V, ‖h‖ = t → ‖fderiv ℝ g v h‖ ≤ 2 * δ + C * t * t := by
    intro h hh
    have hψd : ∀ x, DifferentiableAt ℝ (fun y => g y - fderiv ℝ g v y) x :=
      fun x => (hg x).sub (fderiv ℝ g v).differentiableAt
    have hψf : ∀ x, fderiv ℝ (fun y => g y - fderiv ℝ g v y) x = fderiv ℝ g x - fderiv ℝ g v := by
      intro x
      exact ((hg x).hasFDerivAt.sub (fderiv ℝ g v).hasFDerivAt).fderiv
    have hb : ∀ x ∈ Metric.closedBall v t,
        ‖fderiv ℝ (fun y => g y - fderiv ℝ g v y) x‖ ≤ C * t := by
      intro x hx
      rw [hψf]
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      exact (hL x v).trans (mul_le_mul_of_nonneg_left hx hC)
    have hvh : v + h ∈ Metric.closedBall v t := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hh]
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hψd x) hb
      (convex_closedBall v t) (Metric.mem_closedBall_self ht.le) hvh
    rw [add_sub_cancel_left, hh, map_add] at hmv
    have e1 : g (v + h) - (fderiv ℝ g v v + fderiv ℝ g v h) - (g v - fderiv ℝ g v v) =
        (g (v + h) - g v) - fderiv ℝ g v h := by abel
    rw [e1] at hmv
    have e2 : fderiv ℝ g v h = (g (v + h) - g v) - ((g (v + h) - g v) - fderiv ℝ g v h) := by abel
    rw [e2]
    calc _ ≤ ‖g (v + h) - g v‖ + ‖(g (v + h) - g v) - fderiv ℝ g v h‖ := norm_sub_le _ _
      _ ≤ (δ + δ) + C * t * t :=
          add_le_add ((norm_sub_le _ _).trans (add_le_add (hδ _) (hδ _))) hmv
      _ = 2 * δ + C * t * t := by ring
  have hnn : 0 ≤ 2 * δ / t + C * t := add_nonneg (div_nonneg (by linarith) ht.le) (mul_nonneg hC ht.le)
  refine ContinuousLinearMap.opNorm_le_bound _ hnn (fun u => ?_)
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hs : 0 ≤ t / ‖u‖ := div_nonneg ht.le hu'.le
  have hk := key ((t / ‖u‖) • u) (by rw [norm_smul, Real.norm_of_nonneg hs, div_mul_cancel₀ t hu'.ne'])
  rw [ContinuousLinearMap.map_smul, norm_smul, Real.norm_of_nonneg hs] at hk
  have h3 : ‖fderiv ℝ g v u‖ * t ≤ (2 * δ + C * t * t) * ‖u‖ := by
    have e : ‖fderiv ℝ g v u‖ * t = (t / ‖u‖ * ‖fderiv ℝ g v u‖) * ‖u‖ := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hk hu'.le
  have e3 : (2 * δ / t + C * t) * ‖u‖ = (2 * δ + C * t * t) * ‖u‖ / t := by
    field_simp
  rw [e3, le_div_iff₀ ht]
  exact h3

theorem norm_iteratedFDeriv_sub_le_of_bound {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : V → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) {C : ℝ}
    (hC : ∀ v, ‖iteratedFDeriv ℝ (n + 1) f v‖ ≤ C) (a b : V) :
    ‖iteratedFDeriv ℝ n f a - iteratedFDeriv ℝ n f b‖ ≤ C * ‖a - b‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ n f) (fun x _ => hd x)
    (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hC x) convex_univ (Set.mem_univ b)
    (Set.mem_univ a)

theorem eventually_forall_norm_le_of_lipschitz_of_decay {X V E : Type*} {l : Filter X}
    [NormedAddCommGroup V] [ProperSpace V] [NormedAddCommGroup E] {h : X → V → E}
    (hp : ∀ v, Tendsto (fun x => h x v) l (𝓝 0)) {C D : ℝ} (hC : 0 ≤ C)
    (hL : ∀ᶠ x in l, ∀ a b, ‖h x a - h x b‖ ≤ C * ‖a - b‖)
    (hD : ∀ᶠ x in l, ∀ v, ‖v‖ * ‖h x v‖ ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∀ v, ‖h x v‖ ≤ ε := by
  have hR1 : (1 : ℝ) ≤ max 1 (D / ε) := le_max_left _ _
  have hDR : D ≤ ε * max 1 (D / ε) := by
    calc D = ε * (D / ε) := by field_simp
      _ ≤ ε * max 1 (D / ε) := mul_le_mul_of_nonneg_left (le_max_right _ _) hε.le
  have hη : 0 < ε / (2 * (C + 1)) := div_pos hε (by linarith)
  have hCη : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) two_pos]
    nlinarith
  obtain ⟨S, -, hSfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : V) (max 1 (D / ε))) hη
  have hS : ∀ᶠ x in l, ∀ s ∈ S, ‖h x s‖ < ε / 2 := by
    rw [hSfin.eventually_all]
    intro s _
    have hs := hp s
    rw [tendsto_zero_iff_norm_tendsto_zero] at hs
    exact hs.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hS, hL, hD] with x hxS hxL hxD v
  by_cases hv : ‖v‖ ≤ max 1 (D / ε)
  · have hvb : v ∈ Metric.closedBall (0 : V) (max 1 (D / ε)) := by rwa [mem_closedBall_zero_iff]
    obtain ⟨s, hs, hvs⟩ := Set.mem_iUnion₂.1 (hcover hvb)
    rw [Metric.mem_ball, dist_eq_norm] at hvs
    have e : h x v = h x s + (h x v - h x s) := by abel
    calc ‖h x v‖ = ‖h x s + (h x v - h x s)‖ := by rw [← e]
      _ ≤ ‖h x s‖ + ‖h x v - h x s‖ := norm_add_le _ _
      _ ≤ ε / 2 + C * (ε / (2 * (C + 1))) :=
          add_le_add (hxS s hs).le ((hxL v s).trans (mul_le_mul_of_nonneg_left hvs.le hC))
      _ ≤ ε := by linarith
  · replace hv := not_le.1 hv
    have hvpos : 0 < ‖v‖ := lt_of_lt_of_le one_pos (hR1.trans hv.le)
    have hmul : ‖v‖ * ‖h x v‖ ≤ ‖v‖ * ε := by
      calc ‖v‖ * ‖h x v‖ ≤ D := hxD v
        _ ≤ ε * max 1 (D / ε) := hDR
        _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_left hv.le hε.le
        _ = ‖v‖ * ε := mul_comm _ _
    exact le_of_mul_le_mul_left hmul hvpos

theorem eventually_forall_norm_iteratedFDeriv_le {X V : Type*} {l : Filter X}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {h : X → SchwartzMap V ℂ}
    (hp : ∀ v, Tendsto (fun x => h x v) l (𝓝 0))
    (hb : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (h x) v‖ ≤ C)
    (n : ℕ) : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ v, ‖iteratedFDeriv ℝ n (h x) v‖ ≤ ε := by
  induction n with
  | zero =>
    intro ε hε
    obtain ⟨C, hC0, hCb⟩ := hb 0 1
    obtain ⟨D, -, hDb⟩ := hb 1 0
    refine eventually_forall_norm_le_of_lipschitz_of_decay
      (h := fun x v => iteratedFDeriv ℝ 0 (h x) v) (C := C) (D := D) (fun v => ?_) hC0 ?_ ?_ hε
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_iteratedFDeriv_zero]
      exact tendsto_zero_iff_norm_tendsto_zero.1 (hp v)
    · filter_upwards [hCb] with x hx a b
      exact norm_iteratedFDeriv_sub_le_of_bound ((h x).smooth ⊤) 0 (fun w => by simpa using hx w) a b
    · filter_upwards [hDb] with x hx w
      simpa using hx w
  | succ n ih =>
    intro ε hε
    obtain ⟨C, hC0, hCb⟩ := hb 0 (n + 2)
    have ht : 0 < ε / (2 * (C + 1)) := div_pos hε (by linarith)
    have hCt : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) two_pos]
      nlinarith
    have hδ : 0 < ε * (ε / (2 * (C + 1))) / 4 := by
      have := mul_pos hε ht
      linarith
    filter_upwards [ih _ hδ, hCb] with x hx hxC v
    have hsm := (h x).smooth ⊤
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (h x)) :=
      hsm.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
    have hLip : ∀ a b, ‖fderiv ℝ (iteratedFDeriv ℝ n (h x)) a - fderiv ℝ (iteratedFDeriv ℝ n (h x)) b‖ ≤
        C * ‖a - b‖ := by
      intro a b
      rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply,
        ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
      exact norm_iteratedFDeriv_sub_le_of_bound hsm (n + 1) (fun w => by simpa using hxC w) a b
    have hv := norm_fderiv_le_of_small_of_lipschitz hdiff hC0 ht hLip hx v
    rw [norm_fderiv_iteratedFDeriv] at hv
    have e : 2 * (ε * (ε / (2 * (C + 1))) / 4) / (ε / (2 * (C + 1))) = ε / 2 := by
      field_simp
      ring
    rw [e] at hv
    linarith

theorem schwartz_continuousAt_of_pointwise_of_bounded :
    ∀ {X : Type} [TopologicalSpace X] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : X → SchwartzMap V ℂ) (x0 : X), (∀ v, ContinuousAt (fun x => F x v) x0) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in nhds x0, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x) v‖ ≤ C) → ContinuousAt F x0 := by
  intro X _ V _ _ _ F x0 hc hb
  have hb' : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in nhds x0, ∀ v,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ ≤ C := by
    intro k n
    obtain ⟨C, hC⟩ := hb k n
    refine ⟨max C 0 + SchwartzMap.seminorm ℝ k n (F x0), add_nonneg (le_max_right _ _) (apply_nonneg _ _), ?_⟩
    filter_upwards [hC] with x hx v
    calc _ ≤ SchwartzMap.seminorm ℝ k n (F x - F x0) := SchwartzMap.le_seminorm ℝ k n _ v
      _ ≤ SchwartzMap.seminorm ℝ k n (F x) + SchwartzMap.seminorm ℝ k n (F x0) := map_sub_le_add _ _ _
      _ ≤ _ := add_le_add (SchwartzMap.seminorm_le_bound ℝ k n (F x) (le_max_right _ _)
          (fun w => (hx w).trans (le_max_left _ _))) le_rfl
  have hp : ∀ v, Tendsto (fun x => (F x - F x0) v) (nhds x0) (𝓝 0) := by
    intro v
    have h2 := (hc v).tendsto.sub_const (F x0 v)
    rw [sub_self] at h2
    exact h2
  rw [ContinuousAt, (schwartz_withSeminorms ℝ V ℂ).tendsto_nhds F (F x0)]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨C2, hC20, hC2⟩ := hb' (2 * k) n
  have hη : 0 < ε ^ 2 / (4 * (C2 + 1)) := div_pos (pow_pos hε 2) (by linarith)
  have hCη : C2 * (ε ^ 2 / (4 * (C2 + 1))) ≤ (ε / 2) ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg ε]
  filter_upwards [eventually_forall_norm_iteratedFDeriv_le (h := fun x => F x - F x0) hp hb' n _ hη, hC2]
    with x hx hx2
  show SchwartzMap.seminorm ℝ k n (F x - F x0) < ε
  refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n _ (by linarith : (0 : ℝ) ≤ ε / 2)
    (fun v => ?_)) (by linarith)
  have ha : 0 ≤ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ := by positivity
  have hsq : (‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) ^ 2 ≤ (ε / 2) ^ 2 := by
    have e : (‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) ^ 2 =
        (‖v‖ ^ (2 * k) * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ := by
      rw [pow_mul']
      ring
    rw [e]
    exact (mul_le_mul (hx2 v) (hx v) (norm_nonneg _) hC20).trans hCη
  nlinarith

end GlobalTheory
