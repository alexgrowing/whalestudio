import Formalism.EllipticTorsion.UnitCancel

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.ExponentialCoefficientWeight

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem mul_le {f g : PowerSeries K} {r A B : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {N : ℕ} (hf : ∀ d ≤ N, ‖coeff d f‖ ≤ A * r ^ d) (hg : ∀ d ≤ N, ‖coeff d g‖ ≤ B * r ^ d) :
    ∀ d ≤ N, ‖coeff d (f * g)‖ ≤ (A * B) * r ^ d := by
  intro d hd
  rw [coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro x hx
  have hx : x.1 + x.2 = d := by simpa using hx
  rw [norm_mul, ← hx, pow_add]
  have h1 := hf x.1 (by omega)
  have h2 := hg x.2 (by omega)
  calc ‖coeff x.1 f‖ * ‖coeff x.2 g‖ ≤ (A * r ^ x.1) * (B * r ^ x.2) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = A * B * (r ^ x.1 * r ^ x.2) := by ring

theorem pow_le {f : PowerSeries K} {r A : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A) {N : ℕ}
    (hf : ∀ d ≤ N, ‖coeff d f‖ ≤ A * r ^ d) :
    ∀ m : ℕ, ∀ d ≤ N, ‖coeff d (f ^ m)‖ ≤ A ^ m * r ^ d := by
  intro m
  induction m with
  | zero =>
    intro d hd
    rw [pow_zero, pow_zero, one_mul, coeff_one]
    split_ifs with h
    · subst h; simp
    · rw [norm_zero]; positivity
  | succ k ih =>
    intro d hd
    rw [pow_succ, pow_succ]
    exact mul_le hr (by positivity) hA ih hf d hd

theorem mul_le_strict {f g : PowerSeries K} {r A B : ℝ} (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hB : 0 ≤ B) {n : ℕ} (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf : ∀ d < n, ‖coeff d f‖ ≤ A * r ^ d) (hg : ∀ d < n, ‖coeff d g‖ ≤ B * r ^ d) :
    ‖coeff n (f * g)‖ ≤ (A * B) * r ^ n := by
  rw [coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro x hx
  have hx : x.1 + x.2 = n := by simpa using hx
  rcases Nat.eq_zero_or_pos x.1 with h1 | h1
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hf0, zero_mul, norm_zero]; positivity
  rcases Nat.eq_zero_or_pos x.2 with h2 | h2
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hg0, mul_zero, norm_zero]; positivity
  rw [norm_mul, ← hx, pow_add]
  have e1 := hf x.1 (by omega)
  have e2 := hg x.2 (by omega)
  calc ‖coeff x.1 f‖ * ‖coeff x.2 g‖ ≤ (A * r ^ x.1) * (B * r ^ x.2) :=
        mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
    _ = A * B * (r ^ x.1 * r ^ x.2) := by ring

theorem inv_le {l E : PowerSeries K} {r : ℝ} (hr : 0 < r)
    (hE0 : constantCoeff E = 0) (hl1 : coeff 1 l = 1)
    (hl : ∀ m, 2 ≤ m → ‖coeff m l‖ ≤ r⁻¹ * r ^ m)
    (hsub : l.subst E = X) :
    ∀ n, 1 ≤ n → ‖coeff n E‖ ≤ r⁻¹ * r ^ n := by
  have hS : HasSubst E := HasSubst.of_constantCoeff_zero' hE0
  have hexp : ∀ n, coeff n (X : PowerSeries K) =
      ∑ m ∈ Finset.range (n + 1), coeff m l * coeff n (E ^ m) := by
    intro n
    rw [← hsub, coeff_subst' hS]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) ?_]
    · simp only [smul_eq_mul]
    · intro m hm
      simp only [Function.mem_support] at hm
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hm
      rw [coeff_of_lt_order n, smul_zero]
      exact lt_of_lt_of_le (by exact_mod_cast (by omega : n < m))
        (le_order_pow_of_constantCoeff_eq_zero m hE0)
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have hEb : ∀ d < k + 1, ‖coeff d E‖ ≤ r⁻¹ * r ^ d := by
    intro d hd
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, coeff_zero_eq_constantCoeff_apply, hE0, norm_zero]; positivity
    · exact ih d hd h0
  have hEb' : ∀ d ≤ k, ‖coeff d E‖ ≤ r⁻¹ * r ^ d := fun d hd => hEb d (by omega)
  have hE : coeff (k + 1) E = coeff (k + 1) (X : PowerSeries K) -
      ∑ i ∈ Finset.range k, coeff (i + 2) l * coeff (k + 1) (E ^ (i + 2)) := by
    have h := hexp (k + 1)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    rw [h]
    simp only [zero_add, pow_one, pow_zero, hl1, one_mul, coeff_one, Nat.add_one_ne_zero,
      if_false, mul_zero, add_zero]
    ring
  rw [hE]
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [coeff_X]
    split_ifs with h1
    · have : k = 0 := by omega
      subst this
      rw [norm_one, zero_add, pow_one, inv_mul_cancel₀ hr.ne']
    · rw [norm_zero]; positivity
  · rw [norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul]
    have hpow0 : constantCoeff (E ^ (i + 1)) = 0 := by
      rw [map_pow, hE0, zero_pow (Nat.succ_ne_zero _)]
    have hc : ‖coeff (k + 1) (E ^ (i + 2))‖ ≤ (r⁻¹ * r⁻¹ ^ (i + 1)) * r ^ (k + 1) := by
      rw [pow_succ' E (i + 1)]
      exact mul_le_strict hr.le hri.le (by positivity) hE0 hpow0 hEb
        (fun d hd => pow_le hr.le hri.le hEb' (i + 1) d (by omega))
    have ha := hl (i + 2) (by omega)
    have hone : r ^ (i + 2) * r⁻¹ ^ (i + 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]
    calc ‖coeff (i + 2) l‖ * ‖coeff (k + 1) (E ^ (i + 2))‖
        ≤ (r⁻¹ * r ^ (i + 2)) * ((r⁻¹ * r⁻¹ ^ (i + 1)) * r ^ (k + 1)) :=
          mul_le_mul ha hc (norm_nonneg _) (by positivity)
      _ = r⁻¹ * r ^ (k + 1) * (r ^ (i + 2) * r⁻¹ ^ (i + 2)) := by ring
      _ = r⁻¹ * r ^ (k + 1) := by rw [hone, mul_one]

end Formalism.ELL.ExponentialCoefficientWeight

namespace Formalism.ELL

open Formalism.G

theorem expWeight_of (h : LogWeight.{u}) : ExpWeight.{u} := by
  intro K _ _ _ p q hp hp0 hp1 hq F e l E he hei he1 hegap hlog hE0 _hEl hlE n hn
  have hlw := h K p q hp hp0 hp1 hq F e l he hei he1 hegap hlog
  have hr0 : 0 < ‖(p : K)‖ ^ (-1 / ((q : ℝ) - 1)) := Real.rpow_pos_of_pos hp0 _
  have key : ∀ m : ℕ, (‖(p : K)‖ ^ (-1 / ((q : ℝ) - 1)))⁻¹ *
      (‖(p : K)‖ ^ (-1 / ((q : ℝ) - 1))) ^ m =
        ‖(p : K)‖ ^ (-((m : ℝ) - 1) / ((q : ℝ) - 1)) := by
    intro m
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_neg hp0.le,
      ← Real.rpow_add hp0]
    congr 1
    ring
  have := ExponentialCoefficientWeight.inv_le hr0 hE0 hlog.2.1
    (fun m hm => by rw [key m]; exact hlw m (by omega)) hlE n hn
  rwa [key n] at this

end Formalism.ELL
