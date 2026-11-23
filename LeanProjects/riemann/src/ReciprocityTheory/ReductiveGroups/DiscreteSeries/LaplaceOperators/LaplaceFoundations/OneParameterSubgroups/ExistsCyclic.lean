import Mathlib

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

def formV {m : ℕ} (u v : Fin m → ℝ) : ℝ := ∑ s : Fin m, (-1) ^ (s.val + 1) * u s * v s

theorem formV_symm {m : ℕ} (u v : Fin m → ℝ) : formV u v = formV v u := by
  unfold formV
  exact Finset.sum_congr rfl fun s _ => by ring

theorem sign_prod {m : ℕ} (x : Fin m → ℝ) (hx : StrictAnti x) (s : Fin m) :
    0 < (-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j) := by
  classical
  have habs : ∀ j ∈ univ.erase s, |x s - x j| = (if j < s then -1 else 1) * (x s - x j) := by
    intro j hj
    have hjs : j ≠ s := Finset.ne_of_mem_erase hj
    split_ifs with h
    · have h1 : x s < x j := hx h
      rw [abs_of_neg (by linarith)]
      ring
    · have h2 : s < j := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hjs)
      have h1 : x j < x s := hx h2
      rw [abs_of_pos (by linarith)]
      ring
  have hc : ((univ.erase s).filter (fun j => j < s)).card = s.val := by
    have he : (univ.erase s).filter (fun j => j < s) = Finset.Iio s := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Iio]
      exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
    rw [he, Fin.card_Iio]
  have hprod : ∏ j ∈ univ.erase s, |x s - x j| = (-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j) := by
    rw [Finset.prod_congr rfl habs, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const, one_pow, mul_one, hc]
  rw [← hprod]
  exact Finset.prod_pos fun j hj =>
    abs_pos.2 (sub_ne_zero.2 (hx.injective.ne (Finset.ne_of_mem_erase hj).symm))

private theorem sum_pow_mul_inv_prod_sub_eq_ite {m : ℕ} (x : Fin m → ℝ) (hx : Function.Injective x) (k : ℕ)
    (hk : k < m) :
    ∑ s : Fin m, x s ^ k * (∏ j ∈ univ.erase s, (x s - x j))⁻¹ = if k + 1 = m then 1 else 0 := by
  classical
  have hinj : Set.InjOn x ((univ : Finset (Fin m)) : Set (Fin m)) := fun a _ b _ h => hx h
  have hdeg : (Polynomial.X ^ k : Polynomial ℝ).degree < ((univ : Finset (Fin m)).card : WithBot ℕ) := by
    rw [card_univ, Fintype.card_fin, Polynomial.degree_X_pow]
    exact_mod_cast hk
  have hI := Lagrange.eq_interpolate hinj hdeg
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff (m - 1)) hI
  try simp only at hc
  rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff] at hc
  have hb : ∀ s : Fin m, (Lagrange.basis univ x s).coeff (m - 1) =
      (∏ j ∈ univ.erase s, (x s - x j))⁻¹ := by
    intro s
    simp only [Lagrange.basis, Lagrange.basisDivisor]
    rw [Finset.prod_mul_distrib, ← map_prod, Polynomial.coeff_C_mul]
    have hmon : (∏ j ∈ univ.erase s, (Polynomial.X - Polynomial.C (x j))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
    have hnd : (∏ j ∈ univ.erase s, (Polynomial.X - Polynomial.C (x j))).natDegree = m - 1 := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _]
      simp [Polynomial.natDegree_X_sub_C, card_erase_of_mem]
    rw [← hnd, hmon.coeff_natDegree, mul_one, prod_inv_distrib]
  simp only [Polynomial.coeff_C_mul, hb, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow] at hc
  have e : (m - 1 = k) ↔ (k + 1 = m) := by omega
  simp only [e] at hc
  exact hc.symm

theorem exists_cyclic (r : ℕ) (x : Fin (2 * r + 1) → ℝ) (hx : StrictAnti x) :
    ∃ c : Fin (2 * r + 1) → ℝ, (∀ s, c s ≠ 0) ∧ ∀ i j : ℕ, i + j ≤ 2 * r →
      formV (fun s => x s ^ i * c s) (fun s => x s ^ j * c s) = if i + j = 2 * r then -1 else 0 := by
  classical
  have hP : ∀ s, 0 < (-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j) := fun s => sign_prod x hx s
  have hPne : ∀ s, ∏ j ∈ univ.erase s, (x s - x j) ≠ 0 := fun s h => by
    have h1 := hP s
    rw [h, mul_zero] at h1
    exact lt_irrefl _ h1
  have hq : ∀ s, 0 < (-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j) := fun s => by
    have h1 : (-1 : ℝ) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j) =
        ((-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j)) / (∏ j ∈ univ.erase s, (x s - x j)) ^ 2 := by
      have := hPne s
      first
      | (field_simp; done)
      | (field_simp; ring)
    rw [h1]
    exact div_pos (hP s) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hPne s))))
  refine ⟨fun s => Real.sqrt ((-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j)),
    fun s => (Real.sqrt_pos.2 (hq s)).ne', fun i j hij => ?_⟩
  have hterm : ∀ s : Fin (2 * r + 1),
      (-1 : ℝ) ^ (s.val + 1) * (x s ^ i * Real.sqrt ((-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j))) *
        (x s ^ j * Real.sqrt ((-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j))) =
      -(x s ^ (i + j) * (∏ j ∈ univ.erase s, (x s - x j))⁻¹) := by
    intro s
    have hs := Real.mul_self_sqrt (hq s).le
    have hne := hPne s
    rcases Nat.even_or_odd s.val with he | ho
    · rw [he.neg_one_pow] at hs
      rw [he.neg_one_pow, (he.add_one).neg_one_pow, pow_add]
      linear_combination (-(x s ^ i * x s ^ j)) * hs
    · rw [ho.neg_one_pow] at hs
      rw [ho.neg_one_pow, (ho.add_one).neg_one_pow, pow_add]
      linear_combination (x s ^ i * x s ^ j) * hs
  simp only [formV]
  rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_neg_distrib,
    sum_pow_mul_inv_prod_sub_eq_ite x hx.injective (i + j) (by omega)]
  by_cases h : i + j = 2 * r
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), neg_zero]

theorem exists_dual {m : ℕ} (x c : Fin m → ℝ) (hx : Function.Injective x) (hc : ∀ s, c s ≠ 0)
    (y : Fin m → ℝ) : ∃ v : Fin m → ℝ, ∀ i : Fin m, formV v (fun s => x s ^ i.val * c s) = y i := by
  classical
  have hW : IsUnit (Matrix.vandermonde x)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.det_vandermonde_ne_zero_iff.2 hx).isUnit
  refine ⟨fun s => ((Matrix.vandermonde x)ᵀ⁻¹ *ᵥ y) s / ((-1) ^ (s.val + 1) * c s), fun i => ?_⟩
  have hw : (Matrix.vandermonde x)ᵀ *ᵥ ((Matrix.vandermonde x)ᵀ⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hW, Matrix.one_mulVec]
  conv_rhs => rw [← hw]
  simp only [formV, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h1 : ((-1 : ℝ) ^ (s.val + 1) * c s) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (hc s)
  have h2 := hc s
  first
  | (field_simp; done)
  | (field_simp; ring)

theorem formV_sub_sum {m r : ℕ} (u w : Fin m → ℝ) (k : Fin r → ℝ) (g : Fin r → Fin m → ℝ) :
    formV (fun s => u s - ∑ b, k b * g b s) w = formV u w - ∑ b, k b * formV (g b) w := by
  simp only [formV, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun s _ => by ring

theorem frame (r : ℕ) (x : Fin (2 * r + 1) → ℝ) (hx : StrictAnti x) :
    ∃ (e f : Fin r → Fin (2 * r + 1) → ℝ) (z : Fin (2 * r + 1) → ℝ),
      (∀ a b, formV (e a) (e b) = 0) ∧ (∀ a b, formV (f a) (f b) = 0) ∧
      (∀ a b, formV (f a) (e b) = if a = b then 1 else 0) ∧
      (∀ a, formV (e a) z = 0) ∧ (∀ a, formV (f a) z = 0) ∧ formV z z = -1 ∧
      (∀ a s, x s * e a s = if h : a.val + 1 < r then e ⟨a.val + 1, h⟩ s else z s) := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_cyclic r x hx
  let g : ℕ → Fin (2 * r + 1) → ℝ := fun i s => x s ^ i * c s
  have hG : ∀ i j : ℕ, i + j ≤ 2 * r →
      formV (g i) (g j) = if i + j = 2 * r then -1 else 0 := hc
  have hdual : ∀ a : Fin r, ∃ v : Fin (2 * r + 1) → ℝ, ∀ i : Fin (2 * r + 1),
      formV v (g i.val) = if i.val = a.val then 1 else 0 := fun a =>
    exists_dual x c hx.injective hc0 _
  choose f' hf' using hdual
  let e : Fin r → Fin (2 * r + 1) → ℝ := fun a => g a.val
  let z : Fin (2 * r + 1) → ℝ := g r
  let Q : Fin r → Fin r → ℝ := fun a b => formV (f' a) (f' b)
  let f : Fin r → Fin (2 * r + 1) → ℝ := fun a s => f' a s - ∑ b, (1 / 2 * Q a b) * e b s
  have hee : ∀ a b : Fin r, formV (e a) (e b) = 0 := by
    intro a b
    have := a.isLt
    have := b.isLt
    change formV (g a.val) (g b.val) = 0
    rw [hG _ _ (by omega), if_neg (by omega)]
  have hez : ∀ a : Fin r, formV (e a) z = 0 := by
    intro a
    have := a.isLt
    change formV (g a.val) (g r) = 0
    rw [hG _ _ (by omega), if_neg (by omega)]
  have hzz : formV z z = -1 := by
    change formV (g r) (g r) = -1
    rw [hG _ _ (by omega), if_pos (by omega)]
  have hf'e : ∀ a b : Fin r, formV (f' a) (e b) = if a = b then 1 else 0 := by
    intro a b
    have h := hf' a ⟨b.val, by omega⟩
    change formV (f' a) (g b.val) = _
    rw [show formV (f' a) (g b.val) = if b.val = a.val then 1 else 0 from h]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [if_neg (fun h' => hab (Fin.ext h'.symm)), if_neg hab]
  have hf'z : ∀ a : Fin r, formV (f' a) z = 0 := by
    intro a
    have := a.isLt
    have h := hf' a ⟨r, by omega⟩
    change formV (f' a) (g r) = 0
    rw [show formV (f' a) (g r) = if r = a.val then 1 else 0 from h, if_neg (by omega)]
  have hfe : ∀ a b : Fin r, formV (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    have h1 : formV (f a) (e b) = formV (f' a) (e b) - ∑ c, (1 / 2 * Q a c) * formV (e c) (e b) :=
      formV_sub_sum _ _ _ _
    rw [h1, hf'e]
    simp [hee]
  have hfz : ∀ a : Fin r, formV (f a) z = 0 := by
    intro a
    have h1 : formV (f a) z = formV (f' a) z - ∑ c, (1 / 2 * Q a c) * formV (e c) z :=
      formV_sub_sum _ _ _ _
    rw [h1, hf'z]
    simp [hez]
  have hff : ∀ a b : Fin r, formV (f a) (f b) = 0 := by
    intro a b
    have h1 : formV (f a) (f b) = formV (f' a) (f b) - ∑ c, (1 / 2 * Q a c) * formV (e c) (f b) :=
      formV_sub_sum _ _ _ _
    have h2 : formV (f' a) (f b) = Q b a - ∑ d, (1 / 2 * Q b d) * formV (e d) (f' a) := by
      rw [formV_symm]
      exact formV_sub_sum _ _ _ _
    have h3 : ∀ c, formV (e c) (f b) = if b = c then 1 else 0 := fun c => by
      rw [formV_symm, hfe]
    have h4 : ∀ d, formV (e d) (f' a) = if a = d then 1 else 0 := fun d => by
      rw [formV_symm, hf'e]
    rw [h1, h2]
    simp only [h3, h4, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hQ : Q b a = Q a b := formV_symm _ _
    rw [hQ]
    ring
  refine ⟨e, f, z, hee, hff, hfe, hez, hfz, hzz, fun a s => ?_⟩
  change x s * (x s ^ a.val * c s) = if h : a.val + 1 < r then g (a.val + 1) s else g r s
  split_ifs with h
  · ring
  · have hr : a.val + 1 = r := by omega
    have hp : x s ^ r = x s ^ (a.val + 1) := by rw [hr]
    change x s * (x s ^ a.val * c s) = x s ^ r * c s
    rw [hp]
    ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
