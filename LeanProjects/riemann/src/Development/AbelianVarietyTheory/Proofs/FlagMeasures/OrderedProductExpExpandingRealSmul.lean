import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.ExpChartExpanding

section General
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem norm_exp_sub_one_le (x : A) : ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have h1 := (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have h2 := (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  rw [← Real.exp_eq_exp_ℝ] at h2
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at h1 h2
  refine HasSum.norm_le_of_bounded h1 h2 (fun k => ?_)
  rw [norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos k)) (by positivity)

theorem norm_exp_smul_sub_one_le {E : A} (hE : ‖E‖ ≤ 1) {s t : ℝ} (ht : t ∈ Set.Icc 0 s) :
    ‖NormedSpace.exp (t • E) - 1‖ ≤ Real.exp s - 1 := by
  refine (norm_exp_sub_one_le _).trans ?_
  have : ‖t • E‖ ≤ s := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    nlinarith [ht.1, ht.2, norm_nonneg E]
  linarith [Real.exp_le_exp.2 this]

theorem norm_exp_smul_sub_le {E : A} (hE : ‖E‖ ≤ 1) {s t t' : ℝ} (ht : t ∈ Set.Icc 0 s)
    (ht' : t' ∈ Set.Icc 0 s) :
    ‖NormedSpace.exp (t • E) - NormedSpace.exp (t' • E) - (t - t') • E‖ ≤
      |t - t'| * (Real.exp s - 1) := by
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun u : ℝ => NormedSpace.exp (u • E) - u • E)
    (f' := fun u : ℝ => NormedSpace.exp (u • E) * E - E) (s := Set.Icc 0 s)
    (C := Real.exp s - 1) (x := t') (y := t)
    (fun u _ => by
      have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) E u).sub ((hasDerivAt_id u).smul_const E)
      rw [one_smul] at h
      exact h.hasDerivWithinAt)
    (fun u hu => by
      have h := norm_exp_smul_sub_one_le hE hu
      have e : NormedSpace.exp (u • E) * E - E = (NormedSpace.exp (u • E) - 1) * E := by
        noncomm_ring
      rw [e]
      refine (norm_mul_le _ _).trans ?_
      nlinarith [norm_nonneg E, norm_nonneg (NormedSpace.exp (u • E) - 1)])
    (convex_Icc 0 s) ht' ht
  have e : NormedSpace.exp (t • E) - NormedSpace.exp (t' • E) - (t - t') • E =
      (NormedSpace.exp (t • E) - t • E) - (NormedSpace.exp (t' • E) - t' • E) := by
    rw [sub_smul]; abel
  rw [e, mul_comm]
  simpa [Real.norm_eq_abs] using key

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem norm_mul_le_left {x y : A} {a : ℝ} (hx : ‖x - 1‖ ≤ a - 1) : ‖x * y‖ ≤ a * ‖y‖ := by
  have e : x * y = (x - 1) * y + y := by noncomm_ring
  rw [e]
  have := norm_add_le ((x - 1) * y) y
  have := norm_mul_le (x - 1) y
  nlinarith [norm_nonneg y]

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem norm_mul_le_right {x y : A} {a : ℝ} (hx : ‖x - 1‖ ≤ a - 1) : ‖y * x‖ ≤ ‖y‖ * a := by
  have e : y * x = y * (x - 1) + y := by noncomm_ring
  rw [e]
  have := norm_add_le (y * (x - 1)) y
  have := norm_mul_le y (x - 1)
  nlinarith [norm_nonneg y]

theorem norm_prod_sub_one_le {s : ℝ} : ∀ (m : ℕ) (E : Fin m → A) (t : Fin m → ℝ),
    (∀ i, ‖E i‖ ≤ 1) → (∀ i, t i ∈ Set.Icc 0 s) →
    ‖(List.ofFn fun i => NormedSpace.exp (t i • E i)).prod - 1‖ ≤ Real.exp (m * s) - 1
  | 0, E, t, _, _ => by simp
  | m + 1, E, t, hE, ht => by
    rw [List.ofFn_succ, List.prod_cons]
    have ih := norm_prod_sub_one_le m (fun i => E i.succ) (fun i => t i.succ)
      (fun i => hE _) (fun i => ht _)
    have h0 := norm_exp_smul_sub_one_le (hE 0) (ht 0)
    set P := (List.ofFn fun i : Fin m => NormedSpace.exp (t i.succ • E i.succ)).prod
    set x := NormedSpace.exp (t 0 • E 0)
    have e : x * P - 1 = x * (P - 1) + (x - 1) := by noncomm_ring
    have h1 := norm_mul_le_left (y := P - 1) h0
    have h2 := norm_add_le (x * (P - 1)) (x - 1)
    have h3 : Real.exp (((m + 1 : ℕ) : ℝ) * s) = Real.exp s * Real.exp (m * s) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [e, h3]
    nlinarith [Real.exp_pos s]

theorem norm_sum_smul_le {m : ℕ} (E : Fin m → A) (d : Fin m → ℝ) (hE : ∀ i, ‖E i‖ ≤ 1) :
    ‖∑ i, d i • E i‖ ≤ ∑ i, |d i| := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  nlinarith [abs_nonneg (d i), hE i]

theorem norm_prod_sub_prod_sub_le {s : ℝ} : ∀ (m : ℕ) (E : Fin m → A) (t t' : Fin m → ℝ),
    (∀ i, ‖E i‖ ≤ 1) → (∀ i, t i ∈ Set.Icc 0 s) → (∀ i, t' i ∈ Set.Icc 0 s) →
    ‖(List.ofFn fun i => NormedSpace.exp (t i • E i)).prod -
      (List.ofFn fun i => NormedSpace.exp (t' i • E i)).prod - ∑ i, (t i - t' i) • E i‖ ≤
      (∑ i, |t i - t' i|) * (Real.exp (m * s) - 1)
  | 0, E, t, t', _, _, _ => by simp
  | m + 1, E, t, t', hE, ht, ht' => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ,
      Fin.sum_univ_succ]
    have ih := norm_prod_sub_prod_sub_le m (fun i => E i.succ) (fun i => t i.succ)
      (fun i => t' i.succ) (fun i => hE _) (fun i => ht _) (fun i => ht' _)
    have hP := norm_prod_sub_one_le m (fun i => E i.succ) (fun i => t i.succ)
      (fun i => hE _) (fun i => ht _)
    have hS := norm_sum_smul_le (fun i : Fin m => E i.succ) (fun i => t i.succ - t' i.succ)
      (fun i => hE _)
    have h0 := norm_exp_smul_sub_one_le (hE 0) (ht' 0)
    have h1 := norm_exp_smul_sub_le (hE 0) (ht 0) (ht' 0)
    have hD : ‖(t 0 - t' 0) • E 0‖ ≤ |t 0 - t' 0| := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg (t 0 - t' 0), hE 0]
    have hL : 0 ≤ ∑ i : Fin m, |t i.succ - t' i.succ| := by positivity
    set P := (List.ofFn fun i : Fin m => NormedSpace.exp (t i.succ • E i.succ)).prod
    set P' := (List.ofFn fun i : Fin m => NormedSpace.exp (t' i.succ • E i.succ)).prod
    set x := NormedSpace.exp (t 0 • E 0)
    set x' := NormedSpace.exp (t' 0 • E 0)
    set S := ∑ i : Fin m, (t i.succ - t' i.succ) • E i.succ
    set L := ∑ i : Fin m, |t i.succ - t' i.succ|
    set D := (t 0 - t' 0) • E 0
    have hd := abs_nonneg (t 0 - t' 0)
    set d := |t 0 - t' 0|
    have e : x * P - x' * P' - (D + S) =
        (x - x' - D) * P + D * (P - 1) + x' * (P - P' - S) + (x' - 1) * S := by noncomm_ring
    have h3 : Real.exp (((m + 1 : ℕ) : ℝ) * s) = Real.exp s * Real.exp (m * s) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [e, h3]
    have ha := Real.exp_pos s
    have hb := Real.exp_pos (m * s)
    set a := Real.exp s
    set b := Real.exp (m * s)
    have k1 : ‖(x - x' - D) * P‖ ≤ d * (a - 1) * b :=
      (norm_mul_le_right hP).trans (mul_le_mul_of_nonneg_right h1 hb.le)
    have k2 : ‖D * (P - 1)‖ ≤ d * (b - 1) :=
      (norm_mul_le _ _).trans (mul_le_mul hD hP (norm_nonneg _) hd)
    have k3 : ‖x' * (P - P' - S)‖ ≤ a * (L * (b - 1)) :=
      (norm_mul_le_left h0).trans (mul_le_mul_of_nonneg_left ih ha.le)
    have k4 : ‖(x' - 1) * S‖ ≤ (a - 1) * L :=
      (norm_mul_le _ _).trans (mul_le_mul h0 hS (norm_nonneg _) ((norm_nonneg _).trans h0))
    have k5 := norm_add₄_le (a := (x - x' - D) * P) (b := D * (P - 1)) (c := x' * (P - P' - S))
      (d := (x' - 1) * S)
    nlinarith

end General

theorem hs_eq_trace {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs g = ((g * gᴴ).trace).re := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem hs_sum_smul {n m : ℕ} (E : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, ((E i * (E j)ᴴ).trace).re = if i = j then 1 else 0) (d : Fin m → ℝ) :
    hs (∑ i, d i • E i) = ∑ i, d i ^ 2 := by
  rw [hs_eq_trace, Matrix.conjTranspose_sum, Finset.sum_mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_sum, Complex.re_sum]
  have : ∀ j, ((d i • E i * (d j • E j)ᴴ).trace).re = if i = j then d i * d j else 0 := by
    intro j
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.trace_smul, Complex.smul_re, h]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => this j]
  simp [sq]

section Frob
open scoped Matrix.Norms.Frobenius

theorem sqrt_hs {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs g) = ‖g‖ := by
  rw [Matrix.frobenius_norm_def, hs, Real.sqrt_eq_rpow]
  simp

theorem orderedProductExp_expanding_real_smul (n : ℕ) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (hs0 : 0 ≤ s)
    (h : ∀ i j, ((E i * (E j)ᴴ).trace).re = if i = j then 1 else 0)
    (t t' : Fin (n ^ 2) → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 s ∧ t' i ∈ Set.Icc 0 s) :
    Real.sqrt (∑ i, (t i - t' i) ^ 2) * (1 - n * (Real.exp (3 * n ^ 2 * s) - 1)) ≤
      Real.sqrt (hs ((List.ofFn fun i => NormedSpace.exp (t i • E i)).prod -
        (List.ofFn fun i => NormedSpace.exp (t' i • E i)).prod)) := by
  have hE : ∀ i, ‖E i‖ ≤ 1 := fun i => by
    rw [← sqrt_hs, hs_eq_trace, h]; simp
  have key := norm_prod_sub_prod_sub_le (A := Matrix (Fin n) (Fin n) ℂ) (n ^ 2) E t t' hE
    (fun i => (ht i).1) (fun i => (ht i).2)
  have hS : ‖∑ i, (t i - t' i) • E i‖ = Real.sqrt (∑ i, (t i - t' i) ^ 2) := by
    rw [← sqrt_hs, hs_sum_smul E h]
  have hL : ∑ i, |t i - t' i| ≤ n * Real.sqrt (∑ i, (t i - t' i) ^ 2) := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |t i - t' i|)
    simp only [sq_abs, Finset.card_univ, Fintype.card_fin] at h1
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact_mod_cast h1
  have hb : Real.exp (((n ^ 2 : ℕ) : ℝ) * s) - 1 ≤ Real.exp (3 * n ^ 2 * s) - 1 := by
    have : ((n ^ 2 : ℕ) : ℝ) * s ≤ 3 * n ^ 2 * s := by
      push_cast
      have : 0 ≤ (n : ℝ) ^ 2 * s := by positivity
      linarith
    linarith [Real.exp_le_exp.2 this]
  have hb0 : 0 ≤ Real.exp (((n ^ 2 : ℕ) : ℝ) * s) - 1 := by
    have : 0 ≤ ((n ^ 2 : ℕ) : ℝ) * s := by positivity
    linarith [Real.add_one_le_exp (((n ^ 2 : ℕ) : ℝ) * s)]
  have k := key.trans (mul_le_mul hL hb hb0 (by positivity))
  have fin : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, X = Y →
      ‖X - ∑ i, (t i - t' i) • E i‖ ≤
        n * Real.sqrt (∑ i, (t i - t' i) ^ 2) * (Real.exp (3 * n ^ 2 * s) - 1) →
      Real.sqrt (∑ i, (t i - t' i) ^ 2) * (1 - n * (Real.exp (3 * n ^ 2 * s) - 1)) ≤
        Real.sqrt (hs Y) := by
    rintro X _ rfl hX
    rw [sqrt_hs]
    have tri := norm_sub_norm_le (∑ i, (t i - t' i) • E i) X
    rw [norm_sub_rev, hS] at tri
    linarith
  exact fin _ _ rfl k

end Frob

theorem expanding : ∀ (n : ℕ) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 ≤ s → (∀ i j, ((E i * (E j)ᴴ).trace).re = if i = j then 1 else 0) → ∀ t t' : Fin (n ^ 2) → ℝ, (∀ i, t i ∈ Set.Icc 0 s ∧ t' i ∈ Set.Icc 0 s) → Real.sqrt (∑ i, (t i - t' i) ^ 2) * (1 - n * (Real.exp (3 * n ^ 2 * s) - 1)) ≤ Real.sqrt (hs ((List.ofFn fun i => NormedSpace.exp ((t i : ℂ) • E i)).prod - (List.ofFn fun i => NormedSpace.exp ((t' i : ℂ) • E i)).prod)) := by
  intro n E s hs0 h t t' ht
  simp only [Complex.coe_smul]
  exact orderedProductExp_expanding_real_smul n E s hs0 h t t' ht

end GlobalTheory.ExpChartExpanding
