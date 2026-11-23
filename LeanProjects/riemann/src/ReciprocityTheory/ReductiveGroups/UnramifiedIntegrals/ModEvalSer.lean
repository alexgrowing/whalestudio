import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffRescaleExpandOfNotDvd

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem Conv.summable_norm {f : PowerSeries ℂ} (hf : Conv f) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun n => ‖PowerSeries.coeff n f * x ^ n‖ := by
  refine (hf x hx).congr fun n => ?_
  rw [norm_mul, norm_pow]

theorem Conv.summable {f : PowerSeries ℂ} (hf : Conv f) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun n => PowerSeries.coeff n f * x ^ n := (hf.summable_norm hx).of_norm

theorem Conv.hasSum {f : PowerSeries ℂ} (hf : Conv f) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n f * x ^ n) (ev f x) := (hf.summable hx).hasSum

theorem conv_of_hasSum {f : PowerSeries ℂ}
    (h : ∀ x : ℂ, ‖x‖ < 1 → Summable fun n => PowerSeries.coeff n f * x ^ n) : Conv f := by
  intro x hx
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg x) hxr
  have hr' : r ≠ 0 := hr0.ne'
  have hrn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hs := h (r : ℂ) (by rw [hrn]; exact hr1)
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ hs.tendsto_atTop_zero)
  have hq0 : 0 ≤ ‖x‖ / r := div_nonneg (norm_nonneg _) hr0.le
  have hq : ‖x‖ / r < 1 := (div_lt_one hr0).mpr hxr
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one hq0 hq).mul_left C)
  have h1 : ‖PowerSeries.coeff n f * (r : ℂ) ^ n‖ ≤ C := hC _ ⟨n, rfl⟩
  rw [norm_mul, norm_pow, hrn] at h1
  calc ‖PowerSeries.coeff n f‖ * ‖x‖ ^ n
      = (‖PowerSeries.coeff n f‖ * r ^ n) * (‖x‖ / r) ^ n := by
        rw [div_pow]
        field_simp
    _ ≤ C * (‖x‖ / r) ^ n := mul_le_mul_of_nonneg_right h1 (pow_nonneg hq0 n)

theorem Conv.add {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) : Conv (f + g) := by
  intro x hx
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((hf x hx).add (hg x hx))
  rw [map_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)

theorem Conv.sub {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) : Conv (f - g) := by
  intro x hx
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((hf x hx).add (hg x hx))
  rw [map_sub, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)

theorem coeff_mul_term (f g : PowerSeries ℂ) (x : ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) * x ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * x ^ kl.1) * (PowerSeries.coeff kl.2 g * x ^ kl.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl]
  ring

theorem Conv.mul {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) : Conv (f * g) := by
  intro x hx
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm (hf.summable_norm hx)
    (hg.summable_norm hx)).congr fun n => ?_
  beta_reduce
  rw [← coeff_mul_term, norm_mul, norm_pow]

theorem conv_one : Conv (1 : PowerSeries ℂ) := by
  intro x _
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  rw [Finset.mem_singleton] at hn
  simp [PowerSeries.coeff_one, hn]

theorem ev_one (x : ℂ) : ev (1 : PowerSeries ℂ) x = 1 := by
  unfold ev
  rw [tsum_eq_single 0 (fun n hn => by simp [PowerSeries.coeff_one, hn])]
  simp [PowerSeries.coeff_one]

theorem Conv.pow {f : PowerSeries ℂ} (hf : Conv f) (n : ℕ) : Conv (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact conv_one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem Conv.prod {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ) (hf : ∀ t ∈ s, Conv (f t)) :
    Conv (∏ t ∈ s, f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact conv_one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun t ht => hf t (Finset.mem_insert_of_mem ht))

theorem Conv.C_mul {f : PowerSeries ℂ} (hf : Conv f) (c : ℂ) : Conv (PowerSeries.C c * f) := by
  intro x hx
  refine ((hf x hx).mul_left ‖c‖).congr fun n => ?_
  rw [PowerSeries.coeff_C_mul, norm_mul]
  ring

theorem xp_term (f : PowerSeries ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) (m : ℕ) :
    PowerSeries.coeff (k * m) (xp k f) * x ^ (k * m) = PowerSeries.coeff m f * (x ^ k) ^ m := by
  rw [xp, PowerSeries.coeff_mk, if_pos (dvd_mul_right k m),
    Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hk), pow_mul]

theorem xp_support (f : PowerSeries ℂ) (k : ℕ) (x : ℂ) :
    ∀ n ∉ Set.range (fun m : ℕ => k * m), PowerSeries.coeff n (xp k f) * x ^ n = 0 := by
  intro n hn
  have hkn : ¬ k ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
  rw [xp, PowerSeries.coeff_mk, if_neg hkn, zero_mul]

theorem natMul_injective {k : ℕ} (hk : k ≠ 0) : Function.Injective (fun m : ℕ => k * m) := fun _ _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h

theorem Conv.xp {f : PowerSeries ℂ} (hf : Conv f) {k : ℕ} (hk : k ≠ 0) : Conv (xp k f) := by
  intro x hx
  have hxk : ‖x ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx hk
  have hz : ∀ n ∉ Set.range (fun m : ℕ => k * m),
      ‖PowerSeries.coeff n (ReciprocityTheory.ChartRestriction.L1.xp k f)‖ * ‖x‖ ^ n = 0 := by
    intro n hn
    have hkn : ¬ k ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
    rw [ReciprocityTheory.ChartRestriction.L1.xp, PowerSeries.coeff_mk, if_neg hkn, norm_zero, zero_mul]
  refine ((natMul_injective hk).summable_iff hz).mp ?_
  refine (hf (x ^ k) hxk).congr fun m => ?_
  show ‖PowerSeries.coeff m f‖ * ‖x ^ k‖ ^ m =
    ‖PowerSeries.coeff (k * m) (ReciprocityTheory.ChartRestriction.L1.xp k f)‖ * ‖x‖ ^ (k * m)
  rw [ReciprocityTheory.ChartRestriction.L1.xp, PowerSeries.coeff_mk, if_pos (dvd_mul_right k m),
    Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hk), norm_pow, pow_mul]

theorem Conv.rescale {f : PowerSeries ℂ} (hf : Conv f) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    Conv (PowerSeries.rescale c f) := by
  intro x hx
  have hcx : ‖c * x‖ < 1 := by
    rw [norm_mul]
    calc ‖c‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg x)
      _ < 1 := by rw [one_mul]; exact hx
  refine (hf (c * x) hcx).congr fun n => ?_
  simp only [PowerSeries.coeff_rescale, norm_mul, norm_pow, mul_pow]
  ring

theorem Conv.sub1 {f : PowerSeries ℂ} (hf : Conv f) {c : ℂ} (hc : ‖c‖ ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    Conv (sub1 c k f) := (hf.rescale hc).xp hk

theorem ev_add {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) {x : ℂ} (hx : ‖x‖ < 1) :
    ev (f + g) x = ev f x + ev g x := by
  have h := (hf.hasSum hx).add (hg.hasSum hx)
  have e : (fun n => PowerSeries.coeff n (f + g) * x ^ n) =
      fun n => PowerSeries.coeff n f * x ^ n + PowerSeries.coeff n g * x ^ n := by
    funext n
    rw [map_add, add_mul]
  rw [← e] at h
  exact h.tsum_eq

theorem ev_sub {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) {x : ℂ} (hx : ‖x‖ < 1) :
    ev (f - g) x = ev f x - ev g x := by
  have h := (hf.hasSum hx).sub (hg.hasSum hx)
  have e : (fun n => PowerSeries.coeff n (f - g) * x ^ n) =
      fun n => PowerSeries.coeff n f * x ^ n - PowerSeries.coeff n g * x ^ n := by
    funext n
    rw [map_sub, sub_mul]
  rw [← e] at h
  exact h.tsum_eq

theorem ev_mul {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) {x : ℂ} (hx : ‖x‖ < 1) :
    ev (f * g) x = ev f x * ev g x := by
  unfold ev
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hf.summable_norm hx)
    (hg.summable_norm hx)]
  exact tsum_congr fun n => coeff_mul_term f g x n

theorem ev_pow {f : PowerSeries ℂ} (hf : Conv f) (n : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    ev (f ^ n) x = ev f x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ev_one]
  | succ n ih => rw [pow_succ, pow_succ, ev_mul (hf.pow n) hf hx, ih]

theorem ev_xp (f : PowerSeries ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) : ev (xp k f) x = ev f (x ^ k) := by
  have hsupp : Function.support (fun n => PowerSeries.coeff n (xp k f) * x ^ n) ⊆
      Set.range (fun m : ℕ => k * m) := by
    intro n hn
    by_contra h
    exact hn (xp_support f k x n h)
  unfold ev
  rw [← (natMul_injective hk).tsum_eq hsupp]
  exact tsum_congr fun m => xp_term f hk x m

theorem evalSeries_rescaleExpand (f : PowerSeries ℂ) (c : ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) :
    ev (sub1 c k f) x = ev f (c * x ^ k) := by
  rw [sub1, ev_xp _ hk]
  unfold ev
  exact tsum_congr fun n => by rw [PowerSeries.coeff_rescale, mul_pow]; ring

private theorem eq_zero_at_zero_of_tsum_mul_pow_eq_zero (b : ℕ → ℂ) (hb : Summable fun i => ‖b i‖ * (1 / 2 : ℝ) ^ i)
    (h0 : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∑' i, b i * (t : ℂ) ^ i = 0) : b 0 = 0 := by
  have hK : Summable fun i => ‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i := by
    refine (((summable_nat_add_iff 1).mpr hb).mul_left 2).congr fun i => ?_
    beta_reduce
    ring
  have hmain : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      ‖b 0‖ ≤ t * ∑' i, ‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i := by
    intro t ht hle
    have hbd : ∀ i, ‖b i * (t : ℂ) ^ i‖ ≤ ‖b i‖ * (1 / 2 : ℝ) ^ i := by
      intro i
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hle i) (norm_nonneg _)
    have hGn : Summable fun i => ‖b i * (t : ℂ) ^ i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbd hb
    have hG : Summable fun i => b i * (t : ℂ) ^ i := hGn.of_norm
    have hsplit := hG.tsum_eq_zero_add
    rw [h0 t ht hle, pow_zero, mul_one] at hsplit
    have hb0 : b 0 = -∑' i, b (i + 1) * (t : ℂ) ^ (i + 1) := by linear_combination -hsplit
    have hGn1 : Summable fun i => ‖b (i + 1) * (t : ℂ) ^ (i + 1)‖ :=
      (summable_nat_add_iff 1).mpr hGn
    have hle2 : ∀ i, ‖b (i + 1) * (t : ℂ) ^ (i + 1)‖ ≤ t * (‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i) := by
      intro i
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, pow_succ]
      calc ‖b (i + 1)‖ * (t ^ i * t) = t * (‖b (i + 1)‖ * t ^ i) := by ring
        _ ≤ t * (‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hle i) (norm_nonneg _)) ht.le
    rw [hb0, norm_neg]
    exact (norm_tsum_le_tsum_norm hGn1).trans (hasSum_le hle2 hGn1.hasSum (hK.hasSum.mul_left t))
  generalize hKd : (∑' i, ‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i) = K at hmain
  have hK0 : 0 ≤ K := hKd ▸ tsum_nonneg fun i => by positivity
  by_contra hne
  have hc : 0 < ‖b 0‖ := norm_pos_iff.mpr hne
  have hK1 : (0 : ℝ) < 2 * (K + 1) := by linarith
  have ht : 0 < min (1 / 2 : ℝ) (‖b 0‖ / (2 * (K + 1))) := lt_min (by norm_num) (div_pos hc hK1)
  have h1 := hmain _ ht (min_le_left _ _)
  have h2 : min (1 / 2 : ℝ) (‖b 0‖ / (2 * (K + 1))) * K ≤ ‖b 0‖ / (2 * (K + 1)) * K :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hK0
  have h3 : ‖b 0‖ ≤ ‖b 0‖ / (2 * (K + 1)) * K := h1.trans h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hK1] at h3
  nlinarith [mul_nonneg hc.le hK0]

private theorem coeff_eq_zero_of_ev_eq_zero_of_lower_eq_zero {f : PowerSeries ℂ} (hf : Conv f)
    (h : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = 0) (n : ℕ)
    (ih : ∀ j < n, PowerSeries.coeff j f = 0) : PowerSeries.coeff n f = 0 := by
  have key := eq_zero_at_zero_of_tsum_mul_pow_eq_zero (fun i => PowerSeries.coeff (i + n) f) ?_ ?_
  · simpa using key
  · have h2 : ‖((1 / 2 : ℝ) : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
      norm_num
    have hs := (summable_nat_add_iff n).mpr (hf _ h2)
    rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hs
    refine (hs.mul_left (2 ^ n)).congr fun i => ?_
    beta_reduce
    generalize ‖PowerSeries.coeff (i + n) f‖ = c
    rw [pow_add]
    calc (2 : ℝ) ^ n * (c * ((1 / 2) ^ i * (1 / 2) ^ n)) = c * (1 / 2) ^ i * ((1 / 2) ^ n * 2 ^ n) := by
          ring
      _ = c * (1 / 2) ^ i := by rw [← mul_pow]; norm_num
  · intro t ht hle
    have hx : ‖(t : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
      linarith
    have hx0 : 0 < ‖(t : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
      exact ht
    have hev := h _ hx0 hx
    have hsupp : Function.support (fun j => PowerSeries.coeff j f * (t : ℂ) ^ j) ⊆
        Set.range (fun i : ℕ => i + n) := by
      intro j hj
      by_cases hjn : j < n
      · rw [Function.mem_support] at hj
        exact absurd (by simp [ih j hjn]) hj
      · exact ⟨j - n, Nat.sub_add_cancel (not_lt.mp hjn)⟩
    have e1 : ev f (t : ℂ) = ∑' i, PowerSeries.coeff (i + n) f * (t : ℂ) ^ (i + n) :=
      ((add_left_injective n).tsum_eq hsupp).symm
    have e2 : ∑' i, PowerSeries.coeff (i + n) f * (t : ℂ) ^ (i + n) =
        (t : ℂ) ^ n * ∑' i, PowerSeries.coeff (i + n) f * (t : ℂ) ^ i := by
      rw [← tsum_mul_left]
      exact tsum_congr fun i => by ring
    rw [e1, e2] at hev
    have htn : (t : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast ht.ne')
    exact (mul_eq_zero.mp hev).resolve_left htn

theorem eq_zero_of_ev_eq_zero {f : PowerSeries ℂ} (hf : Conv f)
    (h : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = 0) : f = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | _ n ih => exact coeff_eq_zero_of_ev_eq_zero_of_lower_eq_zero hf h n ih

theorem eq_of_ev_eq {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g)
    (h : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = ev g x) : f = g := by
  have h0 := eq_zero_of_ev_eq_zero (hf.sub hg) fun x hx0 hx1 => by
    rw [ev_sub hf hg hx1, h x hx0 hx1, sub_self]
  exact sub_eq_zero.mp h0

end ReciprocityTheory.ChartRestriction.L1
