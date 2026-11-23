import Mathlib
open MeasureTheory

namespace GlobalTheory.UnitaryChart

open Topology Filter

theorem hasStrictFDerivAt_ofFn_prod {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedRing E] [NormedAlgebra ℝ E] :
    ∀ (N : ℕ) (g : Fin N → F → E) (g' : Fin N → F →L[ℝ] E),
      (∀ i, g i 0 = 1 ∧ HasStrictFDerivAt (g i) (g' i) 0) →
      (List.ofFn fun i => g i 0).prod = 1 ∧
        HasStrictFDerivAt (fun t => (List.ofFn fun i => g i t).prod) (∑ i, g' i) 0 := by
  intro N
  induction N with
  | zero =>
    intro g g' _
    simpa using hasStrictFDerivAt_const (𝕜 := ℝ) (1 : E) (0 : F)
  | succ N ih =>
    intro g g' h
    obtain ⟨h1, h2⟩ := ih (fun i => g i.succ) (fun i => g' i.succ) (fun i => h i.succ)
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    refine ⟨by rw [h1, (h 0).1, mul_one], ?_⟩
    have h3 := (h 0).2.mul' h2
    refine (h3.congr_fderiv ?_)
    ext y
    simp [h1, (h 0).1, add_comm]

theorem unitary_list_prod {E : Type} [Ring E] (σ : E → E) (hm : ∀ a b, σ (a * b) = σ b * σ a)
    (h1 : σ 1 = 1) (l : List E) (hl : ∀ u ∈ l, σ u * u = 1 ∧ u * σ u = 1) :
    σ l.prod * l.prod = 1 ∧ l.prod * σ l.prod = 1 := by
  induction l with
  | nil => simp [h1]
  | cons a l ih =>
    obtain ⟨i1, i2⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
    obtain ⟨a1, a2⟩ := hl a List.mem_cons_self
    rw [List.prod_cons, hm]
    constructor
    · calc σ l.prod * σ a * (a * l.prod) = σ l.prod * (σ a * a) * l.prod := by noncomm_ring
        _ = 1 := by rw [a1, mul_one, i1]
    · calc a * l.prod * (σ l.prod * σ a) = a * (l.prod * σ l.prod) * σ a := by noncomm_ring
        _ = 1 := by rw [i2, mul_one, a2]

theorem eq_of_skew_eq {E : Type} [NormedRing E] [NormedAlgebra ℝ E] {u v u' v' : E}
    (hu : u' * u = 1) (hv : v * v' = 1)
    (h : u - u' = v - v') (nu : ‖1 - u'‖ ≤ 1 / 2) (nv : ‖1 - v'‖ ≤ 1 / 2) : u = v := by
  set w := u - v with hw
  have e1 : w = u' - v' := by
    rw [hw]; exact sub_eq_sub_iff_sub_eq_sub.mp h
  have e2 : u' * w * v' = v' - u' := by
    calc u' * w * v' = (u' * u) * v' - u' * (v * v') := by rw [hw]; noncomm_ring
      _ = v' - u' := by rw [hu, hv, one_mul, mul_one]
  have e3 : (2 : ℝ) • w = (1 - u') * w + w * (1 - v') - (1 - u') * w * (1 - v') := by
    have : (1 - u') * w + w * (1 - v') - (1 - u') * w * (1 - v') = w - u' * w * v' := by
      noncomm_ring
    rw [this, e2, two_smul]
    nth_rewrite 2 [e1]
    abel
  have n0 := norm_nonneg w
  have n1 : ‖(1 - u') * w‖ ≤ 1 / 2 * ‖w‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right nu n0)
  have n2 : ‖w * (1 - v')‖ ≤ ‖w‖ * (1 / 2) :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left nv n0)
  have n3 : ‖(1 - u') * w * (1 - v')‖ ≤ 1 / 2 * ‖w‖ * (1 / 2) :=
    (norm_mul_le _ _).trans (mul_le_mul n1 nv (norm_nonneg _) (by positivity))
  have n4 : 2 * ‖w‖ ≤ ‖(1 - u') * w‖ + ‖w * (1 - v')‖ + ‖(1 - u') * w * (1 - v')‖ := by
    have : ‖(2 : ℝ) • w‖ = 2 * ‖w‖ := by rw [norm_smul]; simp
    rw [← this, e3]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have : ‖w‖ = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem exists_skew_coord {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
    (σ : E →ₗ[ℝ] E) {N : ℕ} (e : Fin N → E) (hσ : ∀ a, σ (σ a) = a)
    (hli : LinearIndependent ℝ e) (he : ∀ i, σ (e i) = -e i)
    (hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) :
    ∃ P : E →L[ℝ] (Fin N → ℝ), (∀ t : Fin N → ℝ, P (∑ i, t i • e i) = t) ∧
      (∀ m, σ m = m → P m = 0) ∧ ∀ u v, P u = P v → u - σ u = v - σ v := by
  let T : (Fin N → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ e
  have hT : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.mpr hli.fintypeLinearCombination_injective
  obtain ⟨Q, hQ⟩ := T.exists_leftInverse_of_injective hT
  have hQT : ∀ t, Q (∑ i, t i • e i) = t := fun t => by
    have := LinearMap.congr_fun hQ t
    simpa [T, Fintype.linearCombination_apply] using this
  let π : E →ₗ[ℝ] E := (1 / 2 : ℝ) • (LinearMap.id - σ)
  have hπ : ∀ m, π m = (1 / 2 : ℝ) • (m - σ m) := fun m => rfl
  refine ⟨LinearMap.toContinuousLinearMap (Q ∘ₗ π), fun t => ?_, fun m hm => ?_, fun u v h => ?_⟩
  · have : σ (∑ i, t i • e i) = -∑ i, t i • e i := by
      simp [map_sum, he]
    change Q (π _) = t
    rw [hπ, this, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
    norm_num
    simpa using hQT t
  · change Q (π _) = 0
    rw [hπ, hm, sub_self, smul_zero, map_zero]
  · change Q (π u) = Q (π v) at h
    have h2 : Q (π (u - v)) = 0 := by rw [map_sub, map_sub, h, sub_self]
    have h3 : σ (π (u - v)) = -π (u - v) := by
      rw [hπ, map_smul, map_sub, hσ, ← smul_neg, neg_sub]
    obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hsp _ h3)
    rw [← hy, hQT] at h2
    have h4 : π (u - v) = 0 := by rw [← hy, h2]; simp
    rw [hπ, smul_eq_zero] at h4
    rcases h4 with h4 | h4
    · norm_num at h4
    · rw [map_sub] at h4
      exact sub_eq_sub_iff_sub_eq_sub.mp (sub_eq_zero.mp h4)

theorem second_kind_chart : ∀ (E : Type) [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E) (N : ℕ) (e : Fin N → E) (c : Fin N → ℝ → E), (∀ a, σ (σ a) = a) → (∀ a b, σ (a * b) = σ b * σ a) → σ 1 = 1 → LinearIndependent ℝ e → (∀ i, σ (e i) = -e i) → (∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) → (∀ i, c i 0 = 1 ∧ HasStrictDerivAt (c i) (e i) 0 ∧ ∀ t, σ (c i t) * c i t = 1 ∧ c i t * σ (c i t) = 1) → ∃ (s S K : ℝ) (W : Set E), 0 < s ∧ 0 ≤ K ∧ W ∈ nhds (1 : E) ∧ ∀ x ∈ W, σ x * x = 1 → x * σ x = 1 → ∃ f : (Fin N → ℝ) → (Fin N → ℝ), (∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖f t‖ ≤ S ∧ (List.ofFn fun i => c i (f t i)).prod * x = (List.ofFn fun i => c i (t i)).prod) ∧ ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∀ t' ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖t - t'‖ ≤ K * ‖f t - f t'‖ := by
  intro E _ _ _ σ N e c hσ hm h1 hli he hsp hc
  set Θ : (Fin N → ℝ) → E := fun t => (List.ofFn fun i => c i (t i)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact (hc i).2.2 _)
  let T : (Fin N → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp (ContinuousLinearMap.proj i)
  have hT : ∀ t, T t = ∑ i, t i • e i := fun t => by simp [T]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    hasStrictFDerivAt_ofFn_prod N (fun i (t : Fin N → ℝ) => c i (t i)) _ (fun i =>
      ⟨(hc i).1, HasStrictFDerivAt.comp (0 : Fin N → ℝ) (g := c i)
        (hc i).2.1.hasStrictFDerivAt
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i).hasStrictFDerivAt⟩)
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_skew_coord σ e hσ hli he hsp
  have hΨ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hΨ0 : P (Θ 0) = 0 := by rw [h0]; exact hP2 _ h1
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  obtain ⟨U₁, hU₁, hA⟩ := hΨ.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
  obtain ⟨L, U₂, hU₂, hL⟩ := hD.exists_lipschitzOnWith
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := by fun_prop
    exact this.eventually_le_const (by simp [h1])
  have hΘt : Tendsto Θ (𝓝 0) (𝓝 1) := h0 ▸ hD.continuousAt
  let U : Set (Fin N → ℝ) := U₁ ∩ U₂ ∩ {t | ‖1 - σ (Θ t)‖ ≤ 1 / 2} ∩ Metric.closedBall 0 1
  have hUn : U ∈ 𝓝 0 :=
    inter_mem (inter_mem (inter_mem hU₁ hU₂) (hΘt.eventually hnear))
      (Metric.closedBall_mem_nhds _ one_pos)
  have hV : (fun t => P (Θ t)) '' U ∈ 𝓝 (0 : Fin N → ℝ) := by
    have := hΨ.map_nhds_eq_of_equiv
    rw [hΨ0] at this
    rw [← this]
    exact image_mem_map hUn
  have hM : Tendsto (fun p : (Fin N → ℝ) × E => Θ p.1 * σ p.2) (𝓝 0 ×ˢ 𝓝 1) (𝓝 1) := by
    have a : Tendsto σ (𝓝 1) (𝓝 1) := by
      simpa [h1] using hσc.tendsto 1
    simpa using (hΘt.comp tendsto_fst).mul (a.comp tendsto_snd)
  have hPM : Tendsto (fun p : (Fin N → ℝ) × E => P (Θ p.1 * σ p.2)) (𝓝 0 ×ˢ 𝓝 1) (𝓝 0) := by
    have a : Tendsto P (𝓝 1) (𝓝 0) := by
      simpa [hP2 _ h1] using P.continuous.tendsto 1
    exact a.comp hM
  obtain ⟨A, hAn, W, hWn, hAW⟩ := Filter.mem_prod_iff.mp ((hM.eventually hnear).and (hPM hV))
  obtain ⟨s, hs, hsA⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (inter_mem hAn hU₁)
  have hcube : ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), t ∈ A ∩ U₁ := by
    intro t ht
    apply hsA
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hs.le]
    intro i
    have := ht i (Set.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  refine ⟨s, 1, 2 * (‖P‖ * (L * (‖(1 : E)‖ + 1))), W ∩ Metric.closedBall 1 1, hs, by positivity,
    inter_mem hWn (Metric.closedBall_mem_nhds _ one_pos), fun x hx hx1 hx2 => ?_⟩
  have hxn : ‖x‖ ≤ ‖(1 : E)‖ + 1 := norm_le_of_mem_closedBall hx.2
  have key : ∀ t : Fin N → ℝ, ∃ y : Fin N → ℝ, t ∈ A → y ∈ U ∧ Θ y * x = Θ t := by
    intro t
    by_cases ht : t ∈ A
    · obtain ⟨k1, y, hy, k2⟩ := hAW (Set.mk_mem_prod ht hx.1)
      refine ⟨y, fun _ => ⟨hy, ?_⟩⟩
      have hv : Θ t * σ x * σ (Θ t * σ x) = 1 := by
        rw [hm, hσ]
        calc Θ t * σ x * (x * σ (Θ t)) = Θ t * (σ x * x) * σ (Θ t) := by noncomm_ring
          _ = 1 := by rw [hx1, mul_one, (hU t).2]
      have := eq_of_skew_eq (hU y).1 hv (hP3 _ _ k2) hy.1.2 k1
      rw [this, mul_assoc, hx1, mul_one]
    · exact ⟨0, fun h => absurd h ht⟩
  choose f hf using key
  refine ⟨f, fun t ht => ?_, fun t ht t' ht' => ?_⟩
  · obtain ⟨a, b⟩ := hf t (hcube t ht).1
    exact ⟨mem_closedBall_zero_iff.mp a.2, b⟩
  · obtain ⟨a, b⟩ := hf t (hcube t ht).1
    obtain ⟨a', b'⟩ := hf t' (hcube t' ht').1
    have k1 := hA t (hcube t ht).2 t' (hcube t' ht').2
    have k2 : ‖t - t'‖ ≤ 2 * ‖P (Θ t) - P (Θ t')‖ := by
      have k3 : ‖t - t'‖ ≤ ‖P (Θ t) - P (Θ t')‖ + ‖P (Θ t) - P (Θ t') - (t - t')‖ := by
        have := norm_sub_le (P (Θ t) - P (Θ t')) (P (Θ t) - P (Θ t') - (t - t'))
        simpa using this
      have k4 : ‖P (Θ t) - P (Θ t') - (t - t')‖ ≤ 1 / 2 * ‖t - t'‖ := by simpa using k1
      linarith
    have k5 : ‖Θ (f t) - Θ (f t')‖ ≤ L * ‖f t - f t'‖ := by
      simpa [dist_eq_norm] using hL.dist_le_mul _ a.1.1.2 _ a'.1.1.2
    have k6 : ‖P (Θ t) - P (Θ t')‖ ≤ ‖P‖ * (L * ‖f t - f t'‖ * (‖(1 : E)‖ + 1)) := by
      rw [← map_sub, ← b, ← b', ← sub_mul]
      refine (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact (norm_mul_le _ _).trans (mul_le_mul k5 hxn (norm_nonneg _) (by positivity))
    calc ‖t - t'‖ ≤ 2 * (‖P‖ * (L * ‖f t - f t'‖ * (‖(1 : E)‖ + 1))) := by linarith
      _ = _ := by ring

end GlobalTheory.UnitaryChart
