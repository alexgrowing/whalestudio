import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonF
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonG

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Regroup

variable {K : Type} [Field K]

theorem hon_regroup (τ : K →+* K) (π : K) (c t w : ℕ → K) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ m, M ≤ m → w m = 0) (ht0 : t 0 = 1)
    (ht : ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i))) :
    ∑ i ∈ Finset.range M, t i * (π * w i - ∑ j ∈ Finset.range M, (τ ^ i) (c j) * w (i + j + 1))
      = π * w 0 - (c 0 - π * t 1) * w 1 := by
  obtain ⟨K', rfl⟩ : ∃ K', M = K' + 1 := ⟨M - 1, by omega⟩

  have hS : ∑ i ∈ Finset.range (K' + 1), ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1)
      = ∑ n ∈ Finset.range (K' + 1), w (n + 1) * ∑ i ∈ Finset.range (n + 1), t i * (τ ^ i) (c (n - i)) := by
    have hA : ∀ i ∈ Finset.range (K' + 1),
        ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1)
          = ∑ j ∈ Finset.range (K' + 1 - i), t i * (τ ^ i) (c j) * w (i + j + 1) := by
      intro i _
      symm
      refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
        fun j _ hj => ?_
      simp only [Finset.mem_range, not_lt] at hj
      rw [hw _ (by omega), mul_zero]
    rw [Finset.sum_congr rfl hA]
    have hflip := Finset.sum_range_diag_flip (K' + 1)
      (fun i j => t i * (τ ^ i) (c j) * w (i + j + 1))
    beta_reduce at hflip
    rw [← hflip]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have e : i + (n - i) + 1 = n + 1 := by omega
    rw [e]
    ring
  have hsplit : ∀ i, t i * (π * w i - ∑ j ∈ Finset.range (K' + 1), (τ ^ i) (c j) * w (i + j + 1))
      = π * (t i * w i) - ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1) := by
    intro i
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have hF : ∀ n ∈ Finset.range K',
      w (n + 1 + 1) * ∑ i ∈ Finset.range (n + 1 + 1), t i * (τ ^ i) (c (n + 1 - i))
        = π * (t (n + 1 + 1) * w (n + 1 + 1)) := by
    intro n _
    have h2 := ht (n + 1 + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h2
    rw [← mul_assoc, h2]
    ring
  have hF0 : w (0 + 1) * ∑ i ∈ Finset.range (0 + 1), t i * (τ ^ i) (c (0 - i)) = c 0 * w 1 := by
    simp [ht0] <;> ring
  have htel := Finset.sum_range_sub' (fun m => t (m + 1) * w (m + 1)) K'
  beta_reduce at htel
  rw [Finset.sum_sub_distrib, zero_add] at htel
  have hwM : w (K' + 1) = 0 := hw _ le_rfl
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib, ← Finset.mul_sum, hS,
    Finset.sum_range_succ', Finset.sum_range_succ']
  try beta_reduce
  rw [Finset.sum_congr rfl hF, ← Finset.mul_sum, hF0, ht0]
  linear_combination π * htel - π * t (K' + 1) * hwM

end Regroup

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] {l : ℕ}
  {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem hon_lt_sq_pow (hl : 2 ≤ l) (n : ℕ) : n < (l ^ 2) ^ n := by
  have h4 : 1 < l ^ 2 := by nlinarith
  first
  | exact Nat.lt_pow_self h4
  | exact Nat.lt_pow_self h4 n

private theorem coeff_subst_X_pow_eq_ite_dvd' (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
  have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
  rw [PowerSeries.coeff_subst' ha]
  simp only [← pow_mul, PowerSeries.coeff_X_pow]
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    rw [finsum_eq_single _ q]
    · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
    · intro d hd
      have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
      simp [this]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    have : m ≠ k * d := fun h => hd ⟨d, h⟩
    simp [this]

theorem hon_series_coeff (hl : 2 ≤ l) (τ : K →+* K) (c : ℕ → K)
    (h : ∀ N : ℕ, ∃ R : PowerSeries K, constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map (τ ^ (i + 1)) lam).subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1))))) (n : ℕ) :
    ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖ := by
  obtain ⟨R, hR0, hR⟩ := h n
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have hRn : coeff n (R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (n + 1)))) = 0 := by
    rw [coeff_subst_X_pow_eq_ite_dvd' R (pow_ne_zero _ hq)]
    split_ifs
    · rw [Nat.div_eq_of_lt (lt_of_lt_of_le (hon_lt_sq_pow hl n)
          (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq) (Nat.le_succ n))),
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hR0]
    · rfl
  have hsum : coeff n (∑ i ∈ Finset.range n, C (c i) *
        (PowerSeries.map (τ ^ (i + 1)) lam).subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1))))
      = ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
          c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam) := by
    rw [map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_C_mul, coeff_subst_X_pow_eq_ite_dvd' _ (pow_ne_zero _ hq)]
    split_ifs
    · rw [PowerSeries.coeff_map]
    · rw [mul_zero]
  unfold DivBy at hR
  have hcoef := hR n
  rw [map_sub, map_sub, PowerSeries.coeff_C_mul, hsum, hRn, sub_zero] at hcoef
  exact hcoef

def twC (l : ℕ) (τ : K →+* K) (lam : PowerSeries K) (n m : ℕ) : K :=
  if (l ^ 2) ^ m ∣ n then (τ ^ m) (coeff (n / (l ^ 2) ^ m) lam) else 0

theorem twC_zero (τ : K →+* K) (n : ℕ) : twC l τ lam n 0 = coeff n lam := by
  simp [twC]

theorem twC_one (τ : K →+* K) (n : ℕ) :
    twC l τ lam n 1 = if l ^ 2 ∣ n then τ (coeff (n / l ^ 2) lam) else 0 := by
  simp [twC]

theorem twC_eq_zero (hl : 2 ≤ l) (τ : K →+* K) (h0 : constantCoeff lam = 0) {n m : ℕ}
    (hnm : n ≤ m) : twC l τ lam n m = 0 := by
  unfold twC
  split_ifs with hd
  · have hlt : n < (l ^ 2) ^ m := lt_of_le_of_lt hnm (hon_lt_sq_pow hl m)
    rw [Nat.div_eq_of_lt hlt, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · rfl

theorem twC_shift (τ : K →+* K) {n i : ℕ} (hd : (l ^ 2) ^ i ∣ n) (j : ℕ) :
    (τ ^ i) (twC l τ lam (n / (l ^ 2) ^ i) j) = twC l τ lam n (i + j) := by
  unfold twC
  simp only [pow_add, RingHom.mul_def, RingHom.comp_apply, Nat.dvd_div_iff_mul_dvd hd,
    Nat.div_div_eq_div_mul]
  split_ifs <;> simp

theorem twC_of_not_dvd (τ : K →+* K) {n i : ℕ} (hd : ¬ (l ^ 2) ^ i ∣ n) (j : ℕ) :
    twC l τ lam n (i + j) = 0 := by
  unfold twC
  rw [if_neg]
  intro h
  exact hd (dvd_trans (pow_dvd_pow _ (Nat.le_add_right i j)) h)

theorem hon_norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hτ, ih]

theorem hon_coeff_unif (hl : 2 ≤ l) (τ : K →+* K) (c : ℕ → K) (h0 : constantCoeff lam = 0)
    (E : ∀ n, ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖) {n M : ℕ} (hM : n ≤ M) :
    ‖(l : K) * coeff n lam - ∑ j ∈ Finset.range M, c j * twC l τ lam n (j + 1)‖ ≤ ‖(l : K)‖ := by
  have h1 : ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)
      = ∑ j ∈ Finset.range n, c j * twC l τ lam n (j + 1) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold twC
    split_ifs <;> simp
  have h2 : ∑ j ∈ Finset.range n, c j * twC l τ lam n (j + 1)
      = ∑ j ∈ Finset.range M, c j * twC l τ lam n (j + 1) := by
    refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
      fun j _ hj => ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [twC_eq_zero hl τ h0 (by omega), mul_zero]
  rw [← h2, ← h1]
  exact E n

theorem hon_coeff_shift (hl : 2 ≤ l) (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (c : ℕ → K)
    (h0 : constantCoeff lam = 0)
    (E : ∀ n, ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖) {n M : ℕ} (hM : n ≤ M)
    (i : ℕ) :
    ‖(l : K) * twC l τ lam n i - ∑ j ∈ Finset.range M, (τ ^ i) (c j) * twC l τ lam n (i + j + 1)‖
      ≤ ‖(l : K)‖ := by
  by_cases hd : (l ^ 2) ^ i ∣ n
  · have e1 : twC l τ lam n i = (τ ^ i) (coeff (n / (l ^ 2) ^ i) lam) := by
      rw [← twC_zero (l := l) τ (n / (l ^ 2) ^ i), twC_shift τ hd 0, add_zero]
    have e2 : ∀ j, twC l τ lam n (i + j + 1) = (τ ^ i) (twC l τ lam (n / (l ^ 2) ^ i) (j + 1)) := by
      intro j
      rw [twC_shift τ hd (j + 1), add_assoc]
    have hn' : n / (l ^ 2) ^ i ≤ M := le_trans (Nat.div_le_self _ _) hM
    have key := hon_coeff_unif hl τ c h0 E hn'
    rw [← hon_norm_pow_apply τ hτ i] at key
    convert key using 2
    rw [map_sub, map_mul, map_natCast, e1, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, e2]
  · have e1 : twC l τ lam n i = 0 := by simpa using twC_of_not_dvd (lam := lam) τ hd 0
    have e2 : ∀ j, twC l τ lam n (i + j + 1) = 0 := fun j => by
      rw [add_assoc]
      exact twC_of_not_dvd τ hd (j + 1)
    simp only [e1, e2, mul_zero, Finset.sum_const_zero, sub_zero, norm_zero]
    exact norm_nonneg _

theorem hon_main (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : K, ‖c‖ = 1 ∧ IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  have hl : 2 ≤ l := hF.prime.two_le
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨c, hc0, hc, hN⟩ := hon_series hF h he0 he hlog hlev
  have hτ : ∀ x, ‖(σ.comp σ) x‖ = ‖x‖ := fun x => (hF.isom _).trans (hF.isom x)
  obtain ⟨t, ht0, htn, ht⟩ := twisted_division (σ.comp σ) hτ (l : K) hF.norm_l c hc0 hc
  have E := hon_series_coeff hl (σ.comp σ) c hN
  have hlt : ‖(l : K) * t 1‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (htn 1)).trans_lt hF.norm_l
  refine ⟨c 0 - (l : K) * t 1, ?_, fun n => ?_⟩
  · rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, hc0]; exact hlt.ne'), norm_neg, hc0]
    exact max_eq_left hlt.le
  · have key := hon_regroup (σ.comp σ) (l : K) c t (twC l (σ.comp σ) lam n) (n + 1) (by omega)
      (fun m hm => twC_eq_zero hl _ h.lam0 (by omega)) ht0 ht
    have bd : ‖(l : K) * twC l (σ.comp σ) lam n 0
        - (c 0 - (l : K) * t 1) * twC l (σ.comp σ) lam n 1‖ ≤ ‖(l : K)‖ := by
      rw [← key]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
      rw [norm_mul]
      exact (mul_le_mul (htn i) (hon_coeff_shift hl _ hτ c h.lam0 E (Nat.le_succ n) i)
        (norm_nonneg _) zero_le_one).trans (one_mul _).le
    rw [twC_zero, twC_one] at bd
    rw [map_sub, coeff_smul, coeff_subst_X_pow (pow_ne_zero _ (by omega)), smul_eq_mul]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have : coeff n lam - (c 0 - (l : K) * t 1) / (l : K) *
        (if l ^ 2 ∣ n then coeff (n / l ^ 2) (PowerSeries.map (σ.comp σ) lam) else 0)
        = ((l : K) * coeff n lam - (c 0 - (l : K) * t 1) *
          (if l ^ 2 ∣ n then (σ.comp σ) (coeff (n / l ^ 2) lam) else 0)) / (l : K) := by
      rw [coeff_map]; field_simp
    rw [this, norm_div]
    exact div_le_one_of_le₀ bd (norm_nonneg _)

end ReciprocityTheory.ChartRestriction.L1
