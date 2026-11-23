import Mathlib

noncomputable section

open Finset Polynomial

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qk_det_eval {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (p : Fin n → R[X])
    (hdeg : ∀ i, (p i).natDegree ≤ i) :
    (Matrix.of fun i j => (p j).eval (v i)).det = (Matrix.vandermonde v).det * ∏ i, (p i).coeff i := by
  have h : (Matrix.of fun i j => (p j).eval (v i)) =
      Matrix.vandermonde v * Matrix.of fun (i j : Fin n) => (p j).coeff i := by
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (hdeg j) j.2),
      ← Fin.sum_univ_eq_sum_range (fun k => (p j).coeff k * v i ^ k)]
    refine sum_congr rfl fun k _ => ?_
    simp [Matrix.vandermonde_apply, mul_comm]
  rw [h, Matrix.det_mul, Matrix.det_of_isUpperTriangular (Matrix.matrixOfPolynomials_blockTriangular p hdeg)]
  rfl

lemma qk_det_shift {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (x : R) :
    (Matrix.of fun (i j : Fin n) => v i ^ (j : ℕ) + x * (v i - 1) ^ (j : ℕ)).det =
      (Matrix.vandermonde v).det * (1 + x) ^ n := by
  have h := qk_det_eval v (fun j : Fin n => (X : R[X]) ^ (j : ℕ) + C x * (X - C 1) ^ (j : ℕ)) (by
    intro i
    refine (natDegree_add_le _ _).trans (max_le (natDegree_X_pow_le _) ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_pow_le.trans ?_
    have := natDegree_X_sub_C_le (1 : R)
    calc (i : ℕ) * (X - C (1 : R)).natDegree ≤ (i : ℕ) * 1 := Nat.mul_le_mul_left _ this
      _ = i := mul_one _)
  have hc : ∀ i : Fin n, ((X : R[X]) ^ (i : ℕ) + C x * (X - C 1) ^ (i : ℕ)).coeff i = 1 + x := by
    intro i
    rw [coeff_add, coeff_X_pow_self, coeff_C_mul]
    have := (monic_X_sub_C (1 : R)).pow (i : ℕ)
    have h2 : ((X - C (1 : R)) ^ (i : ℕ)).coeff i = 1 := by
      nontriviality R
      have h3 : ((X - C (1 : R)) ^ (i : ℕ)).natDegree = (i : ℕ) := by
        rw [(monic_X_sub_C (1 : R)).natDegree_pow, natDegree_X_sub_C, mul_one]
      have h4 := this.coeff_natDegree
      rwa [h3] at h4
    rw [h2, mul_one]
  simp only [hc, prod_const, card_univ, Fintype.card_fin] at h
  rw [← h]
  congr 1
  ext i j
  simp

lemma qk_det_expand {R : Type*} [CommRing R] {n : ℕ} (v w : Fin n → R) (x : R) :
    (Matrix.of fun (i j : Fin n) => v i ^ (j : ℕ) + x * w i ^ (j : ℕ)).det =
      ∑ s : Finset (Fin n), x ^ s.card * (Matrix.vandermonde (s.piecewise w v)).det := by
  have hV : ∀ u : Fin n → R, (Matrix.vandermonde u).det =
      Matrix.detRowAlternating (fun (i j : Fin n) => u i ^ (j : ℕ)) := fun u => rfl
  have h0 : (Matrix.of fun (i j : Fin n) => v i ^ (j : ℕ) + x * w i ^ (j : ℕ)).det =
      Matrix.detRowAlternating ((fun (i : Fin n) => x • fun (j : Fin n) => w i ^ (j : ℕ)) +
        fun (i j : Fin n) => v i ^ (j : ℕ)) := by
    show Matrix.detRowAlternating _ = _
    congr 1
    funext i j
    simp [add_comm]
  rw [h0, AlternatingMap.map_add_univ]
  refine sum_congr rfl fun s _ => ?_
  have h2 : s.piecewise (fun (i : Fin n) => x • fun (j : Fin n) => w i ^ (j : ℕ)) (fun (i j : Fin n) => v i ^ (j : ℕ)) =
      s.piecewise (fun i => (fun _ => x) i • (fun (i j : Fin n) => (s.piecewise w v) i ^ (j : ℕ)) i)
        (fun (i j : Fin n) => (s.piecewise w v) i ^ (j : ℕ)) := by
    funext i
    by_cases hi : i ∈ s
    · simp only [piecewise_eq_of_mem _ _ _ hi]
    · simp only [piecewise_eq_of_notMem _ _ _ hi]
  rw [h2, hV]
  have h3 := (Matrix.detRowAlternating (n := Fin n) (R := R)).toMultilinearMap.map_piecewise_smul (fun _ => x)
    (fun (i j : Fin n) => (s.piecewise w v) i ^ (j : ℕ)) s
  refine Eq.trans h3 ?_
  rw [prod_const, smul_eq_mul]
  rfl

def qk_D {n : ℕ} (v : Fin n → ℝ) : ℝ := ∏ i : Fin n, ∏ j ∈ Ioi i, (v j - v i)

lemma qk_det_C {n : ℕ} (v : Fin n → ℝ) : (Matrix.vandermonde fun i => (C (v i) : ℝ[X])).det = C (qk_D v) := by
  rw [Matrix.det_vandermonde, qk_D]
  simp only [map_prod, map_sub]

theorem qk_D_shift {n : ℕ} (v : Fin n → ℝ) (b : ℕ) :
    ∑ s ∈ powersetCard b (univ : Finset (Fin n)), qk_D (s.piecewise (fun i => v i - 1) v) =
      (n.choose b : ℝ) * qk_D v := by
  have h1 := qk_det_expand (fun i => (C (v i) : ℝ[X])) (fun i => (C (v i) : ℝ[X]) - 1) X
  rw [qk_det_shift, qk_det_C] at h1
  have h2 : ∀ s : Finset (Fin n), (Matrix.vandermonde (s.piecewise (fun i => (C (v i) : ℝ[X]) - 1)
      (fun i => (C (v i) : ℝ[X])))).det = C (qk_D (s.piecewise (fun i => v i - 1) v)) := by
    intro s
    rw [← qk_det_C]
    congr 2
    funext i
    by_cases hi : i ∈ s <;> simp [hi]
  simp only [h2] at h1
  have h3 := congrArg (fun q : ℝ[X] => q.coeff b) h1
  simp only [finsetSum_coeff] at h3
  rw [coeff_C_mul, coeff_one_add_X_pow, mul_comm] at h3
  rw [h3, ← sum_filter_add_sum_filter_not univ (fun s : Finset (Fin n) => s.card = b)]
  have h4 : ∑ s ∈ univ.filter (fun s : Finset (Fin n) => ¬ s.card = b),
      ((X : ℝ[X]) ^ s.card * C (qk_D (s.piecewise (fun i => v i - 1) v))).coeff b = 0 := by
    refine sum_eq_zero fun s hs => ?_
    rw [mul_comm, coeff_C_mul_X_pow, if_neg (fun h => (mem_filter.1 hs).2 h.symm)]
  rw [h4, add_zero]
  have h5 : powersetCard b (univ : Finset (Fin n)) = univ.filter (fun s : Finset (Fin n) => s.card = b) := by
    ext s
    simp [mem_powersetCard]
  rw [h5]
  refine sum_congr rfl fun s hs => ?_
  rw [mul_comm, coeff_C_mul_X_pow, if_pos (mem_filter.1 hs).2.symm]

end Formalism.InvariantFactorPaths.ColumnFamilies
