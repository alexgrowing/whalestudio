import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool}

private theorem hs_eq_ipL (X : Matrix (Fin n) (Fin n) ℂ) : hs X = ipL X X := by
  rw [ipL_apply]
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem hs_nonneg' (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem hs_mul_le (A B : Matrix (Fin n) (Fin n) ℂ) : hs (A * B) ≤ hs A * hs B := by

  have key : ∀ i j, ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 := by
    intro i j
    calc ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ * ‖B k j‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
      _ ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  simp only [Formalism.REAL.hs, Matrix.mul_apply]
  calc ∑ i, ∑ j, ‖∑ k, A i k * B k j‖ ^ 2
        ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ j, ∑ k, ‖B k j‖ ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ k, ∑ j, ‖B k j‖ ^ 2 := by congr 1; exact Finset.sum_comm

private theorem hs_neg' (X : Matrix (Fin n) (Fin n) ℂ) : hs (-X) = hs X := by
  simp only [Formalism.REAL.hs, Matrix.neg_apply, norm_neg]

private theorem hs_inv_eq (X : Matrix (Fin n) (Fin n) ℂ) : hs (Jm ε * Xᴴ * Jm ε) = hs X := by

  have hsign : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := by
    intro a; split_ifs <;> simp
  simp only [Formalism.REAL.hs, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, norm_mul, norm_star, hsign, one_mul, mul_one]
  exact Finset.sum_comm

private theorem hs_sub_add_hs_add_eq_parallelogram (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hs (X - Y) + hs (X + Y) = 2 * hs X + 2 * hs Y := by
  simp only [Formalism.REAL.hs, Matrix.sub_apply, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := parallelogram_law_with_norm ℝ (X i j) (Y i j)
  rw [sq, sq, sq, sq]
  linarith

theorem sum_coord_sq_le_hs_and_hs_le (n d : ℕ) (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (hG : ∀ i, inG ε (E i)) (g : UJ ε)
    (hsp : (uMat g - 1) - Jm ε * (uMat g - 1)ᴴ * Jm ε ∈ Submodule.span ℝ (Set.range E)) :
    ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 ≤ hs (uMat g - 1) ∧
      hs (uMat g - 1) ≤ ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 + hs (uMat g - 1) ^ 2 / 4 := by
  set X := uMat g - 1 with hXdef
  set Y := Jm ε * Xᴴ * Jm ε with hYdef

  have hc : ∀ i, ipL (E i) (X - Y) = 2 * ((X * (E i)ᴴ).trace).re := by
    intro i
    rw [ipL_sub_inv (hG i) X, ipL_apply]
  have hexp : X - Y = ∑ i, ipL (E i) (X - Y) • E i := eq_sum_of_mem_span hE hsp

  have hD : hs (X - Y) = 4 * ∑ i, ((X * (E i)ᴴ).trace).re ^ 2 := by
    have h1 : ipL (X - Y) (X - Y) = ∑ i, ipL (E i) (X - Y) * ipL (E i) (X - Y) := by
      calc ipL (X - Y) (X - Y) = ipL (X - Y) (∑ i, ipL (E i) (X - Y) • E i) :=
            congrArg (fun Z => ipL (X - Y) Z) hexp
        _ = ∑ i, ipL (E i) (X - Y) * ipL (X - Y) (E i) := by
            rw [map_sum]
            simp only [map_smul, smul_eq_mul]
        _ = ∑ i, ipL (E i) (X - Y) * ipL (E i) (X - Y) :=
            Finset.sum_congr rfl fun i _ => by rw [ipL_comm (E i) (X - Y)]
    rw [hs_eq_ipL, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hc i]; ring

  have hS : hs (X + Y) ≤ hs X ^ 2 := by
    have hYX : X + Y = -(Y * X) := add_inv_eq g
    have hYn : hs Y = hs X := hs_inv_eq X
    rw [hYX, hs_neg', sq]
    calc hs (Y * X) ≤ hs Y * hs X := hs_mul_le Y X
      _ = hs X * hs X := by rw [hYn]
  have hpara := hs_sub_add_hs_add_eq_parallelogram X Y
  have hYn : hs Y = hs X := hs_inv_eq X
  have hnn : 0 ≤ hs (X + Y) := hs_nonneg' _
  constructor <;> linarith

end GlobalTheory.NilCov
