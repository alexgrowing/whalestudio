import Mathlib

open Matrix

namespace GlobalTheory

theorem exists_nat_mul_quadratic_lt (N : ℕ) (hN : 1 ≤ N) (a b q c : ℚ) (hq : q < 0) :
    ∃ k : ℕ, a + ((N : ℚ) * k) * b + ((N : ℚ) * k) ^ 2 * q < c := by
  set B : ℚ := (|b| + |a - c| + 1) / (-q) with hB
  have hq' : 0 < -q := by linarith
  have hBpos : 0 < B := div_pos (by positivity) hq'
  obtain ⟨k, hk⟩ := exists_nat_gt B
  refine ⟨k, ?_⟩
  have hk1 : (1 : ℚ) ≤ k := by
    have : (0 : ℚ) < k := lt_trans hBpos hk
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at this)
  have hN1 : (1 : ℚ) ≤ N := by exact_mod_cast hN
  set m : ℚ := (N : ℚ) * k with hm
  have hm1 : 1 ≤ m := by nlinarith
  have hmk : (k : ℚ) ≤ m := by nlinarith
  have hmB : B < m := lt_of_lt_of_le hk hmk
  have h1 : |b| + |a - c| + 1 < m * (-q) := by
    rw [hB, div_lt_iff₀ hq'] at hmB; linarith
  have h2 : m * (|b| + |a - c| + 1) < m * (m * (-q)) := mul_lt_mul_of_pos_left h1 (by linarith)
  have h3 : m * b ≤ m * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) (by linarith)
  have h4 : a - c ≤ |a - c| := le_abs_self _
  have h5 : 0 ≤ (m - 1) * (|a - c| + 1) := mul_nonneg (by linarith) (by positivity)
  nlinarith

private theorem trace_mul_vecMulVec {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℚ) (u w : n → ℚ) : (T * vecMulVec u w).trace = w ⬝ᵥ T.mulVec u := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem trace_transvection_conj {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℚ) (x y : n → ℚ) (t : ℚ) :
    ((1 + t • vecMulVec x y)ᵀ * T * (1 + t • vecMulVec x y)).trace =
      T.trace + t * (x ⬝ᵥ T.mulVec y + y ⬝ᵥ T.mulVec x) +
        t ^ 2 * ((y ⬝ᵥ y) * (x ⬝ᵥ T.mulVec x)) := by
  have hP : (1 + t • vecMulVec x y)ᵀ = 1 + t • vecMulVec y x := by
    rw [transpose_add, transpose_one, transpose_smul, transpose_vecMulVec]
  rw [hP]
  have e : (1 + t • vecMulVec y x) * T * (1 + t • vecMulVec x y) =
      T + t • (T * vecMulVec x y) + t • (vecMulVec y x * T) + (t * t) • (vecMulVec y x * T * vecMulVec x y) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    abel
  rw [e, trace_add, trace_add, trace_add, trace_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, Matrix.trace_mul_comm (vecMulVec y x) T]
  simp only [trace_mul_vecMulVec]
  rw [← Matrix.mulVec_mulVec]
  have hv : ∀ w : n → ℚ, vecMulVec y x *ᵥ w = (x ⬝ᵥ w) • y := by
    intro w
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hv, dotProduct_smul, smul_eq_mul]
  ring

theorem exists_congruence_trace_lt :
    ∀ (g N : ℕ), 2 ≤ g → 1 ≤ N → ∀ T : Matrix (Fin g) (Fin g) ℚ, T.IsSymm →
      (∃ v : Fin g → ℚ, v ⬝ᵥ T.mulVec v < 0) →
      ∀ c : ℚ, ∃ U : Matrix (Fin g) (Fin g) ℤ, U.det = 1 ∧
        (∀ i j, (N : ℤ) ∣ U i j - (1 : Matrix (Fin g) (Fin g) ℤ) i j) ∧
        ((U.map (Int.cast : ℤ → ℚ)).transpose * T * U.map (Int.cast : ℤ → ℚ)).trace < c := by
  intro g N hg hN T _ hv c
  obtain ⟨v, hv⟩ := hv
  set D : ℕ := ∏ i, (v i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (v i).den_pos
  have hden : ∀ i, (v i).den ∣ D := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set xz : Fin g → ℤ := fun i => ((D / (v i).den : ℕ) : ℤ) * (v i).num with hxz
  have hx : ∀ i, ((xz i : ℤ) : ℚ) = (D : ℚ) * v i := by
    intro i
    have hne : ((v i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (v i).den_nz
    simp only [hxz]
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div (hden i) hne, ← Rat.mul_den_eq_num (v i)]
    field_simp
  set x : Fin g → ℚ := fun i => (xz i : ℚ) with hxdef
  have hxv : x = (D : ℚ) • v := funext fun i => by simp [hxdef, hx]
  have hxT : x ⬝ᵥ T *ᵥ x < 0 := by
    rw [hxv, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have : (0 : ℚ) < D := by exact_mod_cast hDpos
    exact mul_neg_of_pos_of_neg (by positivity) hv
  obtain ⟨i0, hi0⟩ : ∃ i0, xz i0 ≠ 0 := by
    by_contra h
    push Not at h
    have : x = 0 := funext fun i => by simp [hxdef, h i]
    rw [this] at hxT
    simp at hxT
  obtain ⟨i1, hi1⟩ := Fintype.exists_ne_of_one_lt_card (by simp; omega) i0
  set yz : Fin g → ℤ := Pi.single i0 (xz i1) - Pi.single i1 (xz i0) with hyz
  have hyx : yz ⬝ᵥ xz = 0 := by
    rw [hyz, sub_dotProduct, single_dotProduct, single_dotProduct]; ring
  set y : Fin g → ℚ := fun j => (yz j : ℚ) with hydef
  have hy1 : y i1 = -(xz i0 : ℚ) := by
    simp [hydef, hyz, Pi.single_apply, hi1]
  have hyy : 0 < y ⬝ᵥ y := by
    have hle : y i1 * y i1 ≤ y ⬝ᵥ y :=
      Finset.single_le_sum (f := fun j => y j * y j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ i1)
    have hpos : 0 < y i1 * y i1 := by
      rw [hy1]
      have : (xz i0 : ℚ) ≠ 0 := by exact_mod_cast hi0
      exact mul_self_pos.mpr (neg_ne_zero.mpr this)
    linarith
  have hq : (y ⬝ᵥ y) * (x ⬝ᵥ T *ᵥ x) < 0 := mul_neg_of_pos_of_neg hyy hxT
  obtain ⟨k, hk⟩ := exists_nat_mul_quadratic_lt N hN T.trace (x ⬝ᵥ T.mulVec y + y ⬝ᵥ T.mulVec x)
    ((y ⬝ᵥ y) * (x ⬝ᵥ T.mulVec x)) c hq
  refine ⟨1 + ((N : ℤ) * k) • vecMulVec xz yz, ?_, ?_, ?_⟩
  · rw [← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
      hyx, smul_zero, add_zero]
  · intro i j
    refine ⟨k * (xz i * yz j), ?_⟩
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    ring
  · have hmap : (1 + ((N : ℤ) * k) • vecMulVec xz yz).map (Int.cast : ℤ → ℚ) =
        1 + ((N : ℚ) * k) • vecMulVec x y := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
        Matrix.one_apply, hxdef, hydef]
      split_ifs <;> push_cast <;> ring
    rw [hmap, trace_transvection_conj]
    exact hk

end GlobalTheory
