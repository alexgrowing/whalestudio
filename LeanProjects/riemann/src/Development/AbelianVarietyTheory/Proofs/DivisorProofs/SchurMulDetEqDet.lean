import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Formalism.ArtinHasse.ArtinHasseProofs.SymmSeries

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.JSW.Bialt

lemma coeff_prod_one_sub_eq_zero {R ι : Type*} [CommRing R] (a : ι → R) (s : Finset ι) :
    ∀ r, s.card < r →
      PowerSeries.coeff r (∏ k ∈ s, (1 - PowerSeries.C (a k) * PowerSeries.X : PowerSeries R)) = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro r hr
    rw [prod_empty, PowerSeries.coeff_one, if_neg (by simp at hr; omega)]
  | insert k s hk ih =>
    intro r hr
    rw [card_insert_of_notMem hk] at hr
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [prod_insert hk, sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, ih _ (by omega), ih _ (by omega), mul_zero, sub_zero]

def ec (n : ℕ) (i : Fin n) (r : ℕ) : MvPolynomial (Fin n) ℤ :=
  PowerSeries.coeff r (∏ k ∈ univ.erase i,
    (1 - PowerSeries.C (MvPolynomial.X k : MvPolynomial (Fin n) ℤ) * PowerSeries.X))

lemma ec_eq_zero {n : ℕ} (i : Fin n) {r : ℕ} (hr : n ≤ r) : ec n i r = 0 := by
  apply coeff_prod_one_sub_eq_zero
  rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have := i.2
  omega

lemma sum_ec_hsymm {n : ℕ} (i : Fin n) (a : ℕ) :
    ∑ r ∈ range (a + 1), ec n i r * MvPolynomial.hsymm (Fin n) ℤ (a - r) = MvPolynomial.X i ^ a := by
  have hAB : (∏ k ∈ univ.erase i,
      (1 - PowerSeries.C (MvPolynomial.X k : MvPolynomial (Fin n) ℤ) * PowerSeries.X)) *
      (∏ j : Fin n, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial (Fin n) ℤ) ^ m)) =
      PowerSeries.mk (fun m => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m) := by
    rw [← prod_erase_mul _ _ (mem_univ i), ← mul_assoc, ← prod_mul_distrib,
      prod_eq_one fun j _ => Formalism.FT.SymmetricSeries.geom_mul _, one_mul]
  have h := congrArg (PowerSeries.coeff a) hAB
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [Formalism.FT.SymmetricSeries.coeff_prod_geom, ec] using h

lemma sum_ec_hsymm' {n : ℕ} (i : Fin n) (a : ℕ) :
    ∑ r ∈ range n, ec n i r * (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      MvPolynomial.X i ^ a := by
  rw [← sum_ec_hsymm i a]
  have h1 : ∑ r ∈ range n, ec n i r * (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      ∑ r ∈ range (n + a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) := by
    refine sum_subset (range_subset_range.2 (by omega)) fun r _ hr => ?_
    rw [ec_eq_zero i (by simpa using hr), zero_mul]
  have h2 : ∑ r ∈ range (a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      ∑ r ∈ range (n + a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) := by
    refine sum_subset (range_subset_range.2 (by omega)) fun r _ hr => ?_
    rw [if_pos (by simp at hr; omega), mul_zero]
  rw [h1, ← h2]
  refine sum_congr rfl fun r hr => ?_
  rw [if_neg (by simp at hr; omega)]

lemma pow_matrix_eq (n : ℕ) (α : Fin n → ℕ) :
    (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (α j)) =
      (Matrix.of fun i m : Fin n => ec n i (n - 1 - m)) *
        (Matrix.of fun m j : Fin n => if α j < n - 1 - m then 0
          else MvPolynomial.hsymm (Fin n) ℤ (α j - (n - 1 - m))) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.of_apply, ← sum_ec_hsymm' i (α j), ← sum_range_reflect,
    ← Fin.sum_univ_eq_sum_range (fun m => ec n i (n - 1 - m) * (if α j < n - 1 - m then 0
          else MvPolynomial.hsymm (Fin n) ℤ (α j - (n - 1 - m))))]
  rfl

lemma det_pow_matrix (n : ℕ) (l : Fin n → ℕ) :
    Matrix.det (Matrix.of fun i j : Fin n =>
      (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) =
      Matrix.det (Matrix.of fun i m : Fin n => ec n i (n - 1 - m)) * schur n l := by
  rw [pow_matrix_eq n (fun j => l j + n - 1 - (j : ℕ)), Matrix.det_mul, schur, ← Matrix.det_transpose (Matrix.of fun i j : Fin n =>
    if ((l i : ℤ) - i + j) < 0 then 0 else MvPolynomial.hsymm (Fin n) ℤ (((l i : ℤ) - i + j).toNat))]
  congr 2
  refine Matrix.ext fun m j => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have hm := m.2
  have hj := j.2
  by_cases h : ((l j : ℤ) - j + m) < 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]
    congr 1
    omega

lemma schur_zero (n : ℕ) : schur n (fun _ => 0) = 1 := by
  rw [schur, Matrix.det_of_upperTriangular]
  · refine prod_eq_one fun i _ => ?_
    simp [MvPolynomial.hsymm_zero]
  · intro i j hij
    have : (j : ℕ) < i := hij
    rw [Matrix.of_apply, if_pos (by push_cast; omega)]

end GlobalTheory.JSW.Bialt

namespace GlobalTheory.JSW

theorem schur_mul_det_eq_det (n : ℕ) (l : Fin n → ℕ) (_hl : Antitone l) :
    schur n l * Matrix.det (Matrix.of fun i j : Fin n =>
        (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) =
      Matrix.det (Matrix.of fun i j : Fin n =>
        (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) := by
  have h0 := Bialt.det_pow_matrix n (fun _ => 0)
  simp only [zero_add, Bialt.schur_zero, mul_one] at h0
  rw [h0, Bialt.det_pow_matrix n l, mul_comm]

end GlobalTheory.JSW
