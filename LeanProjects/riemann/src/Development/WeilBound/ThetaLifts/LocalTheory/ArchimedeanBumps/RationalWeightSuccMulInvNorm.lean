import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ContinuousOnRationalWeight

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate

variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]

abbrev XS (j : Type) : Type := PiLp 2 fun _ : j => ℂ

def pim (ξ : K → ι → n → ℂ) (p : K × (ι → ℂ)) : XS (ι × n) := WithLp.toLp 2 fun j => 2 * (p.2 j.1 * ξ p.1 j.1 j.2)

def bet (ξ : K → ι → n → ℂ) (q : K × XS (ι × n)) : ι → ℂ := fun w => ∑ i, ξ q.1 w i * conj (q.2 (w, i))

omit [TopologicalSpace K] in
theorem pr_bet (ξ : K → ι → n → ℂ) (k : K) (η : XS (ι × n)) (t : ι → ℂ) : pr (bet ξ (k, η)) t = ⟪η, pim ξ (k, t)⟫ := by
  simp only [pr, bet, pim, PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_mul, Complex.re_sum, Finset.mul_sum, Complex.inner]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
  simp; ring

theorem cont_bet {ξ : K → ι → n → ℂ} (h : Continuous ξ) : Continuous (bet ξ) := by unfold bet; fun_prop

theorem bet_le [CompactSpace K] {ξ : K → ι → n → ℂ} (h : Continuous ξ) : ∃ D : ℝ, ∀ k η, ‖bet ξ (k, η)‖ ≤ D * ‖η‖ := by
  obtain ⟨C, hC⟩ := (isCompact_range h).isBounded.exists_norm_le
  refine ⟨Fintype.card n * |C|, fun k η => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_⟩
  refine (norm_sum_le _ _).trans ?_
  rw [mul_assoc, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
  rw [norm_mul, Complex.norm_conj]
  have h1 : ‖ξ k w i‖ ≤ |C| := ((norm_le_pi_norm _ i).trans (norm_le_pi_norm _ w)).trans ((hC _ ⟨k, rfl⟩).trans (le_abs_self C))
  exact mul_le_mul h1 (PiLp.norm_apply_le η (w, i)) (norm_nonneg _) (abs_nonneg _)

theorem exists_lb {α : Type} [TopologicalSpace α] [CompactSpace α] {g : α → ι → ℝ} (h : ∀ w, Continuous fun a => g a w)
    (hp : ∀ a w, 0 < g a w) : ∃ m : ℝ, 0 < m ∧ ∀ a w, m ≤ g a w := by
  letI : TopologicalSpace ι := ⊥
  haveI : DiscreteTopology ι := ⟨rfl⟩
  have hc : Continuous fun q : α × ι => g q.1 q.2 := continuous_prod_of_discrete_right.2 h
  obtain ⟨m, hm, hb⟩ := isCompact_univ.exists_forall_le' hc.continuousOn (a := 0) fun q _ => hp q.1 q.2
  exact ⟨m, hm, fun a w => hb (a, w) trivial⟩

theorem prp_pim [CompactSpace K] {ξ : K → ι → n → ℂ} (h : Continuous ξ) (hne : ∀ k w, ξ k w ≠ 0) (k₁ : K) :
    Prp (pim ξ) (pim ξ (k₁, 1)) := by
  refine ⟨by unfold pim; fun_prop, ⟨_, rfl⟩, ?_⟩
  obtain ⟨m, hm, hb⟩ := exists_lb (g := fun k w => ‖ξ k w‖) (fun w => by fun_prop) fun k w => norm_pos_iff.2 (hne k w)
  refine ⟨m, {p | ∀ w, m / 2 ≤ ‖p.2 w‖ * ‖ξ p.1 w‖} ∩ univ ×ˢ Metric.closedBall 0 ((‖ξ k₁‖ + m) / m), hm, ?_, ?_, fun p hp => ?_⟩
  · refine IsCompact.inter_left (isCompact_univ.prod (isCompact_closedBall _ _)) ?_
    simp only [setOf_forall]
    exact isClosed_iInter fun w => isClosed_le continuous_const (by fun_prop)
  · intro p hp w h0
    have := hp.1 w
    rw [h0, norm_zero, zero_mul] at this
    linarith
  · have key : ∀ w, ‖p.2 w • ξ p.1 w - ξ k₁ w‖ ≤ m / 2 := fun w => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
      have h1 := (PiLp.norm_apply_le (pim ξ p - pim ξ (k₁, 1)) (w, i)).trans ((dist_eq_norm _ _).symm.le.trans hp)
      have h2 : (pim ξ p - pim ξ (k₁, 1)) (w, i) = 2 * (p.2 w • ξ p.1 w - ξ k₁ w) i := by simp [pim]; ring
      rw [h2, norm_mul, Complex.norm_ofNat] at h1
      linarith
    refine ⟨fun w => ?_, trivial, ?_⟩
    · have := norm_sub_norm_le (ξ k₁ w) (p.2 w • ξ p.1 w)
      rw [norm_sub_rev, norm_smul] at this
      linarith [key w, hb k₁ w]
    · rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_
      have := norm_sub_norm_le (p.2 w • ξ p.1 w) (ξ k₁ w)
      rw [norm_smul] at this
      rw [le_div_iff₀ hm]
      nlinarith [key w, hb p.1 w, norm_le_pi_norm (ξ k₁) w, norm_nonneg (p.2 w)]

theorem exists_FT_ne {a : (ι → ℂ) → ℂ} (ha : Continuous a) (hi : Integrable a) (h0 : a 0 ≠ 0) : ∃ t, FT a t ≠ 0 := by
  by_contra hn
  push Not at hn
  let π : (ι → ℂ) → XS ι := fun x => WithLp.toLp 2 fun w => 2 * x w
  have hπ : Continuous π := by fun_prop
  obtain ⟨φ, -, -, hφ⟩ := core_bump volume π hπ 0 (fun x => a x * (a 0)⁻¹) univ (Metric.closedBall 0 1) isOpen_univ
    (ha.mul continuous_const).continuousOn (isCompact_closedBall _ _) (subset_univ _) 1 one_pos (fun x hx => by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_
      have h1 := (PiLp.norm_apply_le (π x) w).trans ((dist_zero_right _).symm.le.trans hx)
      simp only [π, norm_mul, Complex.norm_ofNat] at h1
      linarith [norm_nonneg (x w)]) (fun x hx => by
      have : x = 0 := funext fun w => by simpa [π] using congrArg (fun y : XS ι => y w) hx
      simp [this, h0]) 0 (by ext w; simp [π])
  refine hφ (fourier_vanish _ π hπ.measurable _ (hi.mul_const _) (fun η => ?_) φ)
  simp only [← mul_assoc]
  rw [integral_mul_const]
  have := hn fun w => -conj (η w)
  rw [FT] at this
  refine mul_eq_zero_of_left (Eq.trans ?_ this) _
  congr 1; funext x; congr 2
  simp only [pr, π, PiLp.inner_apply, Complex.inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp; ring

theorem rationalWeight_succ_mul_inv_norm (κ : ι → ℕ) (e : ℕ) {x : ι → ℂ} (hx : ∀ w, x w ≠ 0) :
    r0 κ (e + 1) x * ((∏ w, ‖x w‖ ^ 2 : ℝ) : ℂ)⁻¹ = r0 κ e x := by
  have : ((∏ w, ‖x w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hx).ne'
  rw [mul_inv_eq_iff_eq_mul₀ this]
  push_cast
  rw [r0, r0, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => by ring

theorem rationalWeight_eq_mul_norm_pow (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : r0 κ e x = r0 κ 0 x * ((nm x : ℝ) : ℂ) ^ e := by
  simp only [r0, nm]
  push_cast
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => by ring

omit [TopologicalSpace K] in
theorem Dec.integrable {a : K × (ι → ℂ) → ℂ} (hd : Dec a) (k : K) (ha : Continuous fun x => a (k, x)) : Integrable fun x => a (k, x) := by
  obtain ⟨C, N, -, hC⟩ := hd.bound 0
  exact (integrable_mj.const_mul C).mono' ha.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hC k x 0)

end PositivityTheory.ThKG.Loc.Bump

end
