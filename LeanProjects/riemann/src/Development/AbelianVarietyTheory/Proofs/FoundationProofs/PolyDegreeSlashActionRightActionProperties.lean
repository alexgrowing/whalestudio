import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

noncomputable section

open Polynomial Matrix
open scoped MatrixGroups

namespace GlobalTheory.HeckeFamilyMatrices.SlPAct

abbrev rowA (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)

abbrev rowB (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i • (rowA g ^ i * rowB g ^ (w - i)) := by
  simp [slP, LinearMap.sum_apply, rowA, rowB]

theorem slP_X_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) {i : ℕ} (hi : i ≤ w) :
    slP w g (X ^ i) = rowA g ^ i * rowB g ^ (w - i) := by
  rw [polySlash_apply]
  simp only [coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h

theorem eq_sum_of_mem {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) :
    p = ∑ i ∈ Finset.range (w + 1), C (p.coeff i) * X ^ i := by
  by_cases h0 : p = 0
  · subst h0; simp
  · apply as_sum_range_C_mul_X_pow'
    rw [natDegree_lt_iff_degree_lt h0]
    exact mem_degreeLT.1 hp

theorem mem_of_natDegree_le {w : ℕ} {q : ℂ[X]} (h : q.natDegree ≤ w) : q ∈ degreeLT ℂ (w + 1) := by
  rw [mem_degreeLT]
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le h)

theorem natDegree_rows_le (g : Matrix (Fin 2) (Fin 2) ℤ) {i w : ℕ} (hi : i ≤ w) :
    (rowA g ^ i * rowB g ^ (w - i)).natDegree ≤ w := by
  have hA : (rowA g).natDegree ≤ 1 := natDegree_linear_le
  have hB : (rowB g).natDegree ≤ 1 := natDegree_linear_le
  calc (rowA g ^ i * rowB g ^ (w - i)).natDegree
      ≤ (rowA g ^ i).natDegree + (rowB g ^ (w - i)).natDegree := natDegree_mul_le
    _ ≤ i * 1 + (w - i) * 1 := add_le_add (natDegree_pow_le_of_le i hA) (natDegree_pow_le_of_le _ hB)
    _ = w := by omega

theorem polySlash_mem (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : slP w g p ∈ degreeLT ℂ (w + 1) := by
  rw [polySlash_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (mem_of_natDegree_le ?_)
  exact natDegree_rows_le g (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

theorem polySlash_one (w : ℕ) {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) : slP w 1 p = p := by
  rw [polySlash_apply]
  conv_rhs => rw [eq_sum_of_mem hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_eq_C_mul, rowA, rowB]

theorem polySlash_conj (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) := by
  rw [polySlash_apply, polySlash_apply, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_pow, coeff_map, rowA, rowB]

theorem slP_C_mul_X_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (c : ℂ) {i : ℕ} (hi : i ≤ w) :
    slP w g (C c * X ^ i) = c • (rowA g ^ i * rowB g ^ (w - i)) := by
  rw [← smul_eq_C_mul, map_smul, slP_X_pow w g hi]

theorem polySlash_mul {m n : ℕ} (g : Matrix (Fin 2) (Fin 2) ℤ) {u v : ℂ[X]}
    (hu : u ∈ degreeLT ℂ (m + 1)) (hv : v ∈ degreeLT ℂ (n + 1)) :
    slP (m + n) g (u * v) = slP m g u * slP n g v := by
  have e : u * v = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      C (u.coeff i * v.coeff j) * X ^ (i + j) := by
    conv_lhs => rw [eq_sum_of_mem hu, eq_sum_of_mem hv]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [C_mul, pow_add]; ring
  rw [e, map_sum, polySlash_apply m g u, polySlash_apply n g v, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [slP_C_mul_X_pow _ _ _ (by omega)]
  have : m + n - (i + j) = (m - i) + (n - j) := by omega
  rw [this, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, C_mul, pow_add, pow_add]
  ring

theorem pow_mem {a : ℕ} {u : ℂ[X]} (hu : u ∈ degreeLT ℂ 2) : u ^ a ∈ degreeLT ℂ (a + 1) := by
  apply mem_of_natDegree_le
  have h1 : u.natDegree ≤ 1 := by
    by_cases h0 : u = 0
    · simp [h0]
    · have := (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hu); omega
  calc (u ^ a).natDegree ≤ a * 1 := natDegree_pow_le_of_le a h1
    _ = a := by omega

theorem polySlash_pow (g : Matrix (Fin 2) (Fin 2) ℤ) {u : ℂ[X]} (hu : u ∈ degreeLT ℂ 2) (a : ℕ) :
    slP a g (u ^ a) = slP 1 g u ^ a := by
  induction a with
  | zero =>
    have := slP_X_pow 0 g (i := 0) le_rfl
    simpa using this
  | succ a ih =>
    rw [pow_succ, polySlash_mul g (pow_mem hu) hu, ih, pow_succ]

theorem rowA_mem (g : Matrix (Fin 2) (Fin 2) ℤ) : rowA g ∈ degreeLT ℂ 2 := mem_of_natDegree_le natDegree_linear_le
theorem rowB_mem (g : Matrix (Fin 2) (Fin 2) ℤ) : rowB g ∈ degreeLT ℂ 2 := mem_of_natDegree_le natDegree_linear_le

theorem polySlash_one_linear (h : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℂ) :
    slP 1 h (C x * X + C y) = C x * rowA h + C y * rowB h := by
  have e1 := slP_X_pow 1 h (i := 1) le_rfl
  have e0 := slP_X_pow 1 h (i := 0) (by omega)
  simp only [pow_one, pow_zero, one_mul, mul_one, Nat.sub_self, Nat.sub_zero] at e1 e0
  have e0' : slP 1 h (C y) = C y * rowB h := by
    calc slP 1 h (C y) = slP 1 h (y • (1 : ℂ[X])) := by rw [smul_eq_C_mul, mul_one]
      _ = y • rowB h := by rw [map_smul, e0]
      _ = C y * rowB h := smul_eq_C_mul _
  rw [map_add, e0', ← smul_eq_C_mul, map_smul, e1, smul_eq_C_mul]

theorem polySlash_one_rowA (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (rowA g) = rowA (g * h) := by
  rw [rowA, polySlash_one_linear]
  simp only [rowA, rowB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_one_rowB (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (rowB g) = rowB (g * h) := by
  rw [rowB, polySlash_one_linear]
  simp only [rowA, rowB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_rowA_pow_mul_rowB_pow (g h : Matrix (Fin 2) (Fin 2) ℤ) (a b : ℕ) :
    slP (a + b) h (rowA g ^ a * rowB g ^ b) = rowA (g * h) ^ a * rowB (g * h) ^ b := by
  rw [polySlash_mul h (pow_mem (rowA_mem g)) (pow_mem (rowB_mem g)), polySlash_pow h (rowA_mem g),
    polySlash_pow h (rowB_mem g), polySlash_one_rowA, polySlash_one_rowB]

theorem polySlash_polySlash (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w (g * h) p = slP w h (slP w g p) := by
  rw [polySlash_apply w g p, map_sum, polySlash_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [map_smul]
  congr 1
  have := polySlash_rowA_pow_mul_rowB_pow g h i (w - i)
  rw [Nat.add_sub_cancel' hi'] at this
  exact this.symm

theorem polySlash_act : ∀ (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) →
    slP w g p ∈ degreeLT ℂ (w + 1) ∧ slP w (g * h) p = slP w h (slP w g p) ∧ slP w 1 p = p ∧
      (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) :=
  fun w g h p hp => ⟨polySlash_mem w g p, polySlash_polySlash w g h p, polySlash_one w hp, polySlash_conj w g p⟩

end GlobalTheory.HeckeFamilyMatrices.SlPAct
