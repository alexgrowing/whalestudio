import Development.WeilBound.CoreStatements.FlagImmersions.AltCMul

noncomputable section

open Polynomial

namespace RootFieldNumerics.M5

theorem Maj.nonneg {f : Polynomial ℝ} {c A : ℝ} (h : Maj f c A) : 0 ≤ c := by
  have := h 0
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one] at this
  exact (abs_nonneg _).trans this

theorem Maj.mono {f : Polynomial ℝ} {c A c' A' : ℝ} (h : Maj f c A) (hA : 0 ≤ A) (hc : c ≤ c') (hA' : A ≤ A') :
    Maj f c' A' := by
  intro s
  have h0 := h.nonneg
  refine (h s).trans ?_
  have h1 : A ^ s ≤ A' ^ s := pow_le_pow_left₀ hA hA' s
  have h2 : c * A ^ s ≤ c' * A' ^ s := mul_le_mul hc h1 (pow_nonneg hA s) (h0.trans hc)
  exact div_le_div_of_nonneg_right h2 (Nat.cast_nonneg _)

theorem Maj.zero {c A : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) : Maj 0 c A := by
  intro s
  simp only [coeff_zero, abs_zero]
  positivity

theorem Maj.one : Maj 1 1 0 := by
  intro s
  rcases s with _ | s
  · simp
  · simp [coeff_one]

theorem Maj.add {f g : Polynomial ℝ} {c d A : ℝ} (hf : Maj f c A) (hg : Maj g d A) : Maj (f + g) (c + d) A := by
  intro s
  rw [coeff_add, add_mul, add_div]
  exact (abs_add_le _ _).trans (add_le_add (hf s) (hg s))

theorem Maj.neg {f : Polynomial ℝ} {c A : ℝ} (hf : Maj f c A) : Maj (-f) c A := by
  intro s
  rw [coeff_neg, abs_neg]
  exact hf s

theorem Maj.sub {f g : Polynomial ℝ} {c d A : ℝ} (hf : Maj f c A) (hg : Maj g d A) : Maj (f - g) (c + d) A := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem Maj.C_mul {f : Polynomial ℝ} {c A : ℝ} (hf : Maj f c A) (r : ℝ) (hr : 0 ≤ r) : Maj (C r * f) (r * c) A := by
  intro s
  rw [coeff_C_mul, abs_mul, abs_of_nonneg hr, mul_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hf s) hr

theorem Maj.sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) (c : ι → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ i ∈ s, Maj (f i) (c i) A) : Maj (∑ i ∈ s, f i) (∑ i ∈ s, c i) A := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Maj.zero le_rfl hA
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Maj.mul {f g : Polynomial ℝ} {c A d B : ℝ} (hf : Maj f c A) (hg : Maj g d B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Maj (f * g) (c * d) (A + B) := by
  intro s
  have hc := hf.nonneg
  rw [coeff_mul, (Commute.all A B).add_pow', Finset.mul_sum, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  rw [abs_mul]
  have h1 := mul_le_mul (hf p.1) (hg p.2) (abs_nonneg _) (by positivity)
  refine h1.trans (le_of_eq ?_)
  have hs : p.1 + p.2 = s := by simpa using hp
  subst hs
  have h2 : (((p.1 + p.2).choose p.1 : ℕ) : ℝ) * p.1.factorial * p.2.factorial = (p.1 + p.2).factorial := by
    have := Nat.add_choose_mul_factorial_mul_factorial p.2 p.1
    rw [add_comm p.2 p.1, mul_right_comm] at this
    exact_mod_cast this
  have h3 : (p.1.factorial : ℝ) ≠ 0 := by positivity
  have h4 : (p.2.factorial : ℝ) ≠ 0 := by positivity
  have h5 : (((p.1 + p.2).choose p.1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right _ _)).ne'
  rw [← h2, nsmul_eq_mul]
  field_simp

theorem Maj.prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) (c A : ι → ℝ)
    (h : ∀ i ∈ s, Maj (f i) (c i) (A i)) (hA : ∀ i ∈ s, 0 ≤ A i) :
    Maj (∏ i ∈ s, f i) (∏ i ∈ s, c i) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Maj.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) fun i hi => hA i (Finset.mem_insert_of_mem hi))
      (hA a (Finset.mem_insert_self _ _)) (Finset.sum_nonneg fun i hi => hA i (Finset.mem_insert_of_mem hi))

section Rem

variable {R : Type} [CommRing R]

def rr (w : ℕ → R) : ℕ → ℕ → R[X]
  | 0, N => if N = 0 then 0 else 1
  | _ + 1, 0 => 0
  | m + 1, N + 1 => C (w N) * rr w m (N + 1) + (X - C (w N)) * rr w m N

theorem rr_small (w : ℕ → R) : ∀ m N : ℕ, m < N → rr w m N = X ^ m
  | 0, N, h => by simp [rr, h.ne']
  | m + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | m + 1, N + 1, h => by
    rw [rr, rr_small w m (N + 1) (by omega), rr_small w m N (by omega)]
    ring

theorem rr_eval (w : ℕ → R) : ∀ m N a : ℕ, a < N → (rr w m N).eval (w a) = w a ^ m
  | 0, N, a, h => by simp [rr, show N ≠ 0 by omega]
  | m + 1, 0, a, h => absurd h (Nat.not_lt_zero _)
  | m + 1, N + 1, a, h => by
    rw [rr]
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X]
    rw [rr_eval w m (N + 1) a h]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · rw [rr_eval w m N a h']; ring
    · subst h'; ring

theorem rr_coeff_succ (w : ℕ → R) (m N n : ℕ) : (rr w (m + 1) (N + 1)).coeff (n + 1) =
    w N * (rr w m (N + 1)).coeff (n + 1) + (rr w m N).coeff n - w N * (rr w m N).coeff (n + 1) := by
  rw [rr, sub_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_mul]
  ring

theorem rr_coeff_zero (w : ℕ → R) (m N : ℕ) : (rr w (m + 1) (N + 1)).coeff 0 =
    w N * (rr w m (N + 1)).coeff 0 - w N * (rr w m N).coeff 0 := by
  rw [rr, sub_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_mul_zero]
  ring

theorem rr_coeff_big (w : ℕ → R) : ∀ m N n : ℕ, N ≤ n → (rr w m N).coeff n = 0
  | 0, N, n, h => by
    rw [rr]
    split_ifs with h0
    · simp
    · rw [coeff_one, if_neg (by omega)]
  | m + 1, 0, n, h => by simp [rr]
  | m + 1, N + 1, 0, h => absurd h (by omega)
  | m + 1, N + 1, n + 1, h => by
    rw [rr_coeff_succ, rr_coeff_big w m (N + 1) (n + 1) h, rr_coeff_big w m N n (by omega),
      rr_coeff_big w m N (n + 1) (by omega)]
    ring

end Rem

def cnt (n d N : ℕ) : ℕ :=
  if n < N then (if d = 0 then 1 else (n + d).choose n * (d - 1).choose (N - 1 - n)) else 0

theorem cnt_two (n d e : ℕ) (he : e ≤ d) :
    cnt n d (n + e + 1) + cnt n d (n + e) = (n + d).choose n * d.choose e := by
  unfold cnt
  rw [if_pos (by omega : n < n + e + 1), show n + e + 1 - 1 - n = e by omega]
  rcases e with _ | e
  · rw [if_neg (by omega : ¬ n < n + 0)]
    split_ifs with h
    · simp [h]
    · simp
  · obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [if_pos (by omega : n < n + (e + 1)), show n + (e + 1) - 1 - n = e by omega,
      if_neg (by omega : ¬ d + 1 = 0), if_neg (by omega : ¬ d + 1 = 0), Nat.add_sub_cancel, Nat.choose_succ_succ' d e]
    ring

theorem cnt_top (n d e : ℕ) : cnt n (d + 1) (n + e + 1) = (n + d + 1).choose n * d.choose e := by
  unfold cnt
  rw [if_pos (by omega : n < n + e + 1), show n + e + 1 - 1 - n = e by omega, if_neg (by omega : ¬ d + 1 = 0),
    Nat.add_sub_cancel, add_assoc]

theorem rr_maj (U : ℝ) (hU : 0 < U) (w : ℕ → Polynomial ℝ) (hw : ∀ a, Maj (w a) U (1 / U)) :
    ∀ m n d N : ℕ, m = n + d → Maj ((rr w m N).coeff n) (cnt n d N * U ^ d) (d / U) := by
  intro m
  induction m with
  | zero =>
    intro n d N h
    obtain rfl : n = 0 := by omega
    obtain rfl : d = 0 := by omega
    rcases N with _ | N
    · simpa [rr, cnt] using Maj.zero le_rfl le_rfl
    · simpa [rr, cnt] using Maj.one
  | succ m ih =>
    intro n d N h
    by_cases h1 : N ≤ n
    · rw [rr_coeff_big w _ _ _ h1]
      exact Maj.zero (by positivity) (by positivity)
    by_cases h2 : m + 1 < N
    · rw [rr_small w _ _ h2, coeff_X_pow]
      split_ifs with h3
      · obtain rfl : d = 0 := by omega
        simpa [cnt, show n < N by omega] using Maj.one
      · exact Maj.zero (by positivity) (by positivity)
    obtain ⟨e, rfl⟩ : ∃ e, N = n + e + 1 := ⟨N - n - 1, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hm : m = n + d := by omega
    have he : e ≤ d := by omega
    have hA : (1 / U + (d : ℝ) / U) = ((d + 1 : ℕ) : ℝ) / U := by push_cast; ring
    have t1 := (hw (n + e)).mul (ih n d (n + e + 1) hm) (by positivity) (by positivity)
    have t3 := (hw (n + e)).mul (ih n d (n + e) hm) (by positivity) (by positivity)
    rw [hA] at t1 t3
    have c2 : (cnt n d (n + e + 1) : ℝ) + cnt n d (n + e) = (n + d).choose n * d.choose e := by
      exact_mod_cast cnt_two n d e he
    rw [cnt_top]
    rcases n with _ | n
    · rw [rr_coeff_zero]
      refine (t1.sub t3).mono (by positivity) (le_of_eq ?_) le_rfl
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at c2 ⊢
      rw [← c2]; ring
    · rw [rr_coeff_succ]
      have t2 := ih n (d + 1) (n + 1 + e) (by omega)
      rw [show n + 1 + e = n + e + 1 by omega, cnt_top, show n + e + 1 = n + 1 + e by omega] at t2
      refine ((t1.add t2).sub t3).mono (by positivity) (le_of_eq ?_) le_rfl
      rw [Nat.choose_succ_succ' (n + 1 + d) n, show n + d + 1 = n + 1 + d by omega]
      push_cast at c2 ⊢
      linear_combination (U ^ (d + 1)) * c2

end RootFieldNumerics.M5
