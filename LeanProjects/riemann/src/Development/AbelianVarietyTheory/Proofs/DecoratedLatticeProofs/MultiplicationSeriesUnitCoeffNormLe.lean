import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega

noncomputable section

namespace GlobalTheory.Honda

open PowerSeries

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem htform_norm_sum_lt {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ j ∈ s, ‖f j‖ < 1) :
    ‖∑ j ∈ s, f j‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (h a (by simp)) (ih fun j hj => h j (by simp [hj])))

theorem htform_norm_sum_le {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ j ∈ s, ‖f j‖ ≤ 1) :
    ‖∑ j ∈ s, f j‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le (h a (by simp)) (ih fun j hj => h j (by simp [hj])))

def HtSmallTo (N : ℕ) (f : K⟦X⟧) : Prop := CoefLe 1 f ∧ ∀ n < N, ‖coeff n f‖ < 1

theorem HtSmallTo.mul {a b : ℕ} {f g : K⟦X⟧} (hf : HtSmallTo a f) (hg : HtSmallTo b g) :
    HtSmallTo (a + b) (f * g) := by
  constructor
  · intro n
    rw [coeff_mul]
    apply htform_norm_sum_le
    rintro ⟨i, j⟩ _
    rw [norm_mul]
    exact mul_le_one₀ (hf.1 i) (norm_nonneg _) (hg.1 j)
  · intro n hn
    rw [coeff_mul]
    apply htform_norm_sum_lt
    rintro ⟨i, j⟩ hij
    have hs : i + j = n := by simpa using hij
    rw [norm_mul]
    by_cases hi : i < a
    · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hf.2 i hi) (hg.1 j)
    · have hj : j < b := by omega
      exact mul_lt_one_of_nonneg_of_lt_one_right (hf.1 i) (norm_nonneg _) (hg.2 j hj)

theorem htSmallTo_zero_iff (f : K⟦X⟧) : HtSmallTo 0 f ↔ CoefLe 1 f :=
  ⟨fun h => h.1, fun h => ⟨h, fun n hn => absurd hn (Nat.not_lt_zero _)⟩⟩

theorem htSmallTo_one : HtSmallTo 0 (1 : K⟦X⟧) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [coeff_one]
  split_ifs <;> simp

theorem htSmallTo_pow {f : K⟦X⟧} (hf : HtSmallTo 0 f) (d : ℕ) : HtSmallTo 0 (f ^ d) := by
  induction d with
  | zero => simpa using htSmallTo_one
  | succ d ih => simpa [pow_succ] using ih.mul hf

theorem htSmallTo_X_pow (k : ℕ) : HtSmallTo 0 ((X : K⟦X⟧) ^ k) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [coeff_X_pow]
  split_ifs <;> simp

theorem htSmallTo_C_mul {c : K} (hc : ‖c‖ ≤ 1) {f : K⟦X⟧} (hf : HtSmallTo 0 f) :
    HtSmallTo 0 (C c * f) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [coeff_C_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hf.1 n)

theorem htSmallTo_sum {ι : Type} (s : Finset ι) (f : ι → K⟦X⟧) (h : ∀ j ∈ s, HtSmallTo 0 (f j)) :
    HtSmallTo 0 (∑ j ∈ s, f j) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [map_sum]
  exact htform_norm_sum_le _ _ fun j hj => (h j hj).1 n

theorem htSmallTo_sub {f g : K⟦X⟧} (hf : HtSmallTo 0 f) (hg : HtSmallTo 0 g) : HtSmallTo 0 (f - g) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [map_sub, sub_eq_add_neg]
  exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (hf.1 n) (by rw [norm_neg]; exact hg.1 n))

theorem htSmallTo_inv {B : K⟦X⟧} (hB : CoefLe 1 B) (h0 : constantCoeff B = 1) : HtSmallTo 0 B⁻¹ := by
  rw [htSmallTo_zero_iff]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [coeff_inv]
  split_ifs with hn
  · simp [h0]
  · rw [h0, inv_one, neg_mul, one_mul, norm_neg]
    apply htform_norm_sum_le
    rintro ⟨i, j⟩ _
    dsimp only
    split_ifs with hj
    · rw [norm_mul]
      exact mul_le_one₀ (hB i) (norm_nonneg _) (ih j hj)
    · simp

theorem htform_coeff_vpow_eq_zero {v : K⟦X⟧} (h0 : constantCoeff v = 0) {n d : ℕ} (h : n < d) :
    coeff n (v ^ d) = 0 := by
  obtain ⟨w, rfl⟩ := X_dvd_iff.mpr h0
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

theorem htform_coeff_subst (A v : K⟦X⟧) (h0 : constantCoeff v = 0) (n : ℕ) :
    coeff n (A.subst v) = ∑ d ∈ Finset.range (n + 1), coeff d A * coeff n (v ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' h0)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hd (by rw [htform_coeff_vpow_eq_zero h0 (by omega), smul_zero])

theorem htSmallTo_subst {A v : K⟦X⟧} (hA : CoefLe 1 A) (hv : CoefLe 1 v) (h0 : constantCoeff v = 0) :
    HtSmallTo 0 (A.subst v) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [htform_coeff_subst A v h0]
  apply htform_norm_sum_le
  intro d _
  rw [norm_mul]
  exact mul_le_one₀ (hA d) (norm_nonneg _) ((htSmallTo_pow ((htSmallTo_zero_iff v).2 hv) d).1 n)

theorem htform_constantCoeff_subst (A v : K⟦X⟧) (h0 : constantCoeff v = 0) :
    constantCoeff (A.subst v) = constantCoeff A := by
  rw [← coeff_zero_eq_constantCoeff_apply, htform_coeff_subst A v h0]
  simp

theorem htform_unit_coeff_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (A v : K⟦X⟧) (e e' : K) (M : ℕ) (Dp Np : Polynomial K), CoefLe 1 A → constantCoeff A = 1 → CoefLe 1 v → constantCoeff v = 0 → ‖e‖ ≤ 1 → ‖e'‖ ≤ 1 → Np.Monic → Np.natDegree = M + 1 → (∀ i, ‖Np.coeff i‖ ≤ 1) → Dp.natDegree ≤ M → ‖Dp.eval e'‖ = 1 → (A.subst v - C e * v ^ 2) * (∑ i ∈ Finset.range (M + 1), C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i))) * X ^ 2 = v ^ 2 * ∑ i ∈ Finset.range (M + 2), C (Np.coeff i) * A ^ i * X ^ (2 * (M + 1 - i)) → ∃ n, n ≤ M + 1 ∧ ‖coeff n v‖ = 1 := by
  intro K _ _ _ A v e e' M Dp Np hA hA0 hv hv0 he he' _ _ hNc hDdeg hDe heq
  by_contra hcon
  push_neg at hcon
  have hvs : HtSmallTo (M + 2) v := ⟨hv, fun n hn => lt_of_le_of_ne (hv n) (hcon n (by omega))⟩
  have hA' : HtSmallTo 0 A := (htSmallTo_zero_iff A).2 hA
  have hB : HtSmallTo 0 (A.subst v - C e * v ^ 2) :=
    htSmallTo_sub (htSmallTo_subst hA hv hv0) (htSmallTo_C_mul he (htSmallTo_pow ((htSmallTo_zero_iff v).2 hv) 2))
  have hB0 : constantCoeff (A.subst v - C e * v ^ 2) = 1 := by
    rw [map_sub, htform_constantCoeff_subst A v hv0, hA0, map_mul, map_pow, hv0]
    simp
  have hH : HtSmallTo 0 (∑ i ∈ Finset.range (M + 2), C (Np.coeff i) * A ^ i * X ^ (2 * (M + 1 - i))) :=
    htSmallTo_sum _ _ fun i _ => by
      simpa using (htSmallTo_C_mul (hNc i) (htSmallTo_pow hA' i)).mul (htSmallTo_X_pow (K := K) (2 * (M + 1 - i)))
  have h1 := ((hvs.mul hvs).mul hH)
  rw [← pow_two, ← heq] at h1
  set G := ∑ i ∈ Finset.range (M + 1), C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i)) with hG
  set B := A.subst v - C e * v ^ 2 with hBdef
  have h2 : HtSmallTo (M + 2 + (M + 2)) (G * X ^ 2) := by
    have := (htSmallTo_inv hB.1 hB0).mul h1
    have hBB : B⁻¹ * (B * G * X ^ 2) = G * X ^ 2 := by
      rw [mul_assoc, ← mul_assoc B⁻¹, PowerSeries.inv_mul_cancel _ (by rw [hB0]; exact one_ne_zero), one_mul]
    rw [hBB, zero_add, add_zero] at this
    exact this
  have h3 : ∀ n < 2 * M + 2, ‖coeff n G‖ < 1 := by
    intro n hn
    have := h2.2 (n + 2) (by omega)
    rwa [coeff_mul_X_pow] at this
  have hterm : ∀ k i, coeff (2 * k) (C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i))) =
      Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0) := by
    intro k i
    rw [mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  have hsmall : ∀ k, k ≤ M → ‖Dp.coeff (M - k)‖ < 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk
    have hc := h3 (2 * k) (by omega)
    rw [hG, map_sum] at hc
    simp_rw [hterm k] at hc
    have hmem : M - k ∈ Finset.range (M + 1) := Finset.mem_range.2 (by omega)
    rw [← Finset.add_sum_erase _ _ hmem] at hc
    have hself : Dp.coeff (M - k) * (if 2 * (M - (M - k)) ≤ 2 * k then coeff (2 * k - 2 * (M - (M - k))) (A ^ (M - k)) else 0)
        = Dp.coeff (M - k) := by
      rw [if_pos (by omega), show 2 * k - 2 * (M - (M - k)) = 0 by omega, coeff_zero_eq_constantCoeff_apply,
        map_pow, hA0, one_pow, mul_one]
    rw [hself] at hc
    have hrest : ‖∑ i ∈ (Finset.range (M + 1)).erase (M - k),
        Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0)‖ < 1 := by
      apply htform_norm_sum_lt
      intro i hi
      rw [Finset.mem_erase, Finset.mem_range] at hi
      split_ifs with hle
      · have hlt : M - i < k := by omega
        have := ih (M - i) hlt (by omega)
        rw [show M - (M - i) = i by omega] at this
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) this ((htSmallTo_pow hA' i).1 _)
      · simp
    have hd : Dp.coeff (M - k) = (Dp.coeff (M - k) + ∑ i ∈ (Finset.range (M + 1)).erase (M - k),
        Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0)) +
        -(∑ i ∈ (Finset.range (M + 1)).erase (M - k),
        Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0)) := by ring
    rw [hd]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hc (by rw [norm_neg]; exact hrest))
  have hev : ‖Dp.eval e'‖ < 1 := by
    rw [Polynomial.eval_eq_sum_range' (n := M + 1) (by omega)]
    apply htform_norm_sum_lt
    intro i hi
    rw [Finset.mem_range] at hi
    have := hsmall (M - i) (by omega)
    rw [show M - (M - i) = i by omega] at this
    rw [norm_mul, norm_pow]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) this (pow_le_one₀ (norm_nonneg _) he')
  rw [hDe] at hev
  exact lt_irrefl _ hev

end GlobalTheory.Honda
