import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul

open Matrix Complex
open scoped Real

namespace GlobalTheory.HilbertThetaSeries

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dotProduct_transpose_mul_diagonal_mul_mulVec (P : Matrix ι ι ℝ) (t : ι → ℂ) (x : ι → ℝ) :
    (fun i => (x i : ℂ)) ⬝ᵥ ((P.map ofReal)ᵀ * diagonal t * P.map ofReal) *ᵥ (fun i => (x i : ℂ)) =
      ∑ j, t j * (((P *ᵥ x) j : ℝ) : ℂ) ^ 2 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    ← ofReal_mulVec_eq P x]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem siegelGaussIntegral_transpose_mul_diagonal_mul {P : Matrix ι ι ℝ} (hP : P.det ≠ 0)
    {t : ι → ℂ} (ht : ∀ i, 0 < (t i).im) :
    siegelGaussIntegral ((P.map ofReal)ᵀ * diagonal t * P.map ofReal) =
      (|P.det⁻¹| : ℝ) * ∏ i, (π / (-(π * I * t i))) ^ (1 / 2 : ℂ) := by
  have hb (i : ι) : 0 < (-(π * I * t i)).re := by simpa using mul_pos Real.pi_pos (ht i)
  have key := GaussianFourier.integral_cexp_neg_sum_mul_add hb fun _ => 0
  have hc := integral_comp_mulVec_of_det_ne_zero hP (f := fun y : ι → ℝ =>
    cexp (-∑ i, -(π * I * t i) * (y i : ℂ) ^ 2 + ∑ i, (0 : ℂ) * y i)) (by fun_prop)
  rw [key] at hc
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Complex.exp_zero,
    mul_one] at hc
  rw [← hc, siegelGaussIntegral]
  congr 2 with x
  rw [dotProduct_transpose_mul_diagonal_mul_mulVec]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, zero_mul, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem tsum_cexp_diagonal_gaussian {B : Matrix ι ι ℝ} (hB : B.det ≠ 0) (u : ι → ℝ) {z : ι → ℂ}
    (hz : ∀ i, 0 < (z i).im) :
    ∑' m : ι → ℤ, cexp (π * I * ∑ j, (-(z j)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) =
      ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ j, (-I * z j) ^ (1 / 2 : ℂ)) *
        ∑' m : ι → ℤ, cexp (π * I * ∑ j, z j * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) *
          cexp (2 * π * I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  have hz0 (i : ι) : z i ≠ 0 := fun h0 => by simpa [h0] using hz i
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht (i : ι) : 0 < (-(z i)⁻¹).im := by
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos (hz i) (normSq_pos.2 (hz0 i))
  have ht0 (i : ι) : -(z i)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero (hz0 i))
  have h := (isSiegel_diagonal_iff.2 ht).transpose_mul_mul hB
  have key := h.riemannTheta_eq_neg_inv (B⁻¹ *ᵥ u) 0
  rw [siegelGaussIntegral_transpose_mul_diagonal_mul hB ht, riemannTheta, riemannTheta] at key
  simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one,
    riemannThetaTerm_def] at key
  have hinv : ((B.map ofReal)ᵀ * diagonal (fun i => -(z i)⁻¹) * B.map ofReal)⁻¹ =
      ((B⁻¹ᵀ).map ofReal)ᵀ * diagonal (fun i => -z i) * (B⁻¹ᵀ).map ofReal := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_diagonal_of_ne_zero ht0,
      ← transpose_nonsing_inv, inv_map_ofReal hB, transpose_map, transpose_transpose,
      Matrix.mul_assoc]
    simp
  rw [hinv] at key
  have hc : ((|B.det⁻¹| : ℝ) : ℂ) * ∏ i, (π / -(π * I * -(z i)⁻¹)) ^ (1 / 2 : ℂ) =
      ((|B.det| : ℝ) : ℂ)⁻¹ * ∏ j, (-I * z j) ^ (1 / 2 : ℂ) := by
    rw [abs_inv, ofReal_inv]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    field_simp [hz0 i]
    simp
  rw [hc] at key
  refine (tsum_congr fun m => ?_).trans (key.trans (congrArg _ (tsum_congr fun m => ?_)))
  · have e := dotProduct_transpose_mul_diagonal_mul_mulVec B (fun i => -(z i)⁻¹)
      ((fun i => (m i : ℝ)) + B⁻¹ *ᵥ u)
    rw [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hB.isUnit, one_mulVec] at e
    simp only [Pi.add_apply, ofReal_add, ofReal_intCast] at e
    rw [e]
    simp only [Pi.zero_apply, ofReal_zero, add_zero, dotProduct, mul_zero, Finset.sum_const_zero,
      ofReal_add]
    congr 1
    ring
  · have e := dotProduct_transpose_mul_diagonal_mul_mulVec B⁻¹ᵀ (fun i => -z i)
      (fun i => (m i : ℝ))
    have e2 : (B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) ⬝ᵥ u = (fun i => (m i : ℝ)) ⬝ᵥ B⁻¹ *ᵥ u := by
      rw [mulVec_transpose, dotProduct_mulVec]
    simp only [ofReal_intCast] at e
    simp only [Pi.zero_apply, ofReal_zero, add_zero, zero_add]
    rw [neg_mulVec, dotProduct_neg, e, ← Complex.exp_add, ← ofReal_sum]
    change _ = cexp (_ + 2 * π * I * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) ⬝ᵥ u : ℝ) : ℂ))
    rw [e2]
    simp only [dotProduct, neg_mul, Finset.sum_neg_distrib, ofReal_sum, ofReal_mul, ofReal_intCast]
    congr 1
    ring

end General

theorem tsum_cexp_block_gaussian : ∀ (V κ : Type) [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ] (k : ℕ), Fintype.card κ = 2 * k → ∀ (B : Matrix (V × κ) (V × κ) ℝ), B.det ≠ 0 → ∀ (u : V × κ → ℝ) (z : V → ℂ), (∀ v, 0 < (z v).im) → ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-(z j.1)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) = ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ v, (-Complex.I * z v)) ^ k * ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, z j.1 * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  intro V κ _ _ _ _ k hk B hB u z hz
  rw [tsum_cexp_diagonal_gaussian hB u (z := fun j => z j.1) fun j => hz j.1]
  congr 2
  rw [Fintype.prod_prod_type, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Finset.prod_const, Finset.card_univ, hk]
  rw [pow_mul, one_div, cpow_ofNat_inv_pow]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_gaussian_constant_on_even_blocks : ∀ (V κ : Type) [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ] (k : ℕ), Fintype.card κ = 2 * k → ∀ (B : Matrix (V × κ) (V × κ) ℝ), B.det ≠ 0 → ∀ (u : V × κ → ℝ) (z : V → ℂ), (∀ v, 0 < (z v).im) → ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-(z j.1)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) = ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ v, (-Complex.I * z v)) ^ k * ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, z j.1 * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian | exact GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian | (intros; apply GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian <;> assumption)
