import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton.GaussDet

theorem integral_exp_sq : ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.integral_exp_neg_rpow (p := 2) (by norm_num)
  simp only [Real.rpow_two] at h
  rw [h]
  norm_num

theorem integral_sq_exp_sq : ∫ z : ℂ, ‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow (p := 2) (q := 2) (by norm_num) (by norm_num)
  simp only [Real.rpow_two] at h
  rw [h]
  norm_num

theorem integrable_exp_sq : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) :=
  Integrable.of_integral_ne_zero (by rw [integral_exp_sq]; exact Real.pi_ne_zero)

theorem integrable_sq_exp_sq : Integrable (fun z : ℂ => ‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :=
  Integrable.of_integral_ne_zero (by rw [integral_sq_exp_sq]; exact Real.pi_ne_zero)

def hf (p q : Prop) [Decidable p] [Decidable q] (z : ℂ) : ℂ :=
  (if p then z else 1) * (if q then conj z else 1) * (Real.exp (-‖z‖ ^ 2) : ℂ)

theorem continuous_hf (p q : Prop) [Decidable p] [Decidable q] : Continuous (hf p q) := by
  unfold hf
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false] <;> fun_prop

theorem integrable_hf (p q : Prop) [Decidable p] [Decidable q] : Integrable (hf p q) := by
  refine Integrable.mono' (integrable_exp_sq.add integrable_sq_exp_sq)
    (continuous_hf p q).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  have he : 0 < Real.exp (-‖z‖ ^ 2) := Real.exp_pos _
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hn : ‖((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ = Real.exp (-‖z‖ ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hb : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  simp only [hf, norm_mul, hn, Pi.add_apply]
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false, norm_one, Complex.norm_conj] <;>
    nlinarith [mul_le_mul_of_nonneg_right hb he.le, mul_pos he he, mul_nonneg (sq_nonneg ‖z‖) he.le]

theorem hf_neg_of_ne (p q : Prop) [Decidable p] [Decidable q] (h : ¬ (p ↔ q)) (z : ℂ) :
    hf p q (-z) = - hf p q z := by
  unfold hf
  by_cases hp : p <;> by_cases hq : q <;> simp_all

theorem integral_hf (p q : Prop) [Decidable p] [Decidable q] :
    ∫ z, hf p q z = if p ↔ q then (Real.pi : ℂ) else 0 := by
  by_cases h : p ↔ q
  · rw [if_pos h]
    by_cases hp : p
    · have hq : q := h.1 hp
      have : hf p q = fun z : ℂ => ((‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
        funext z
        simp only [hf, hp, hq, if_true, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      simp_rw [this]
      rw [integral_complex_ofReal, integral_sq_exp_sq]
    · have hq : ¬ q := fun hq => hp (h.2 hq)
      have : hf p q = fun z : ℂ => ((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
        funext z
        simp only [hf, hp, hq, if_false, one_mul]
      simp_rw [this]
      rw [integral_complex_ofReal, integral_exp_sq]
  · rw [if_neg h]
    have h1 : ∫ z, hf p q (-z) = ∫ z, hf p q z := integral_neg_eq_self _ _
    simp only [hf_neg_of_ne p q h, integral_neg] at h1
    have h2 : (2 : ℂ) * ∫ z, hf p q z = 0 := by linear_combination -h1
    simpa using h2

variable {β : Type} [Fintype β] [DecidableEq β]

def eR (r : β → ℂ) : ℂ := (Real.exp (-∑ k, ‖r k‖ ^ 2) : ℂ)

theorem row_prod (i j : β) (r : β → ℂ) :
    r i * conj (r j) * eR r = ∏ k, hf (k = i) (k = j) (r k) := by
  simp only [hf, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true, eR]
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  push_cast
  rfl

theorem integrable_row (i j : β) :
    Integrable (fun r : β → ℂ => r i * conj (r j) * eR r) := by
  simp_rw [row_prod, volume_pi]
  exact Integrable.fintype_prod (f := fun k : β => hf (k = i) (k = j)) (μ := fun _ => volume)
    fun k => integrable_hf _ _

theorem integral_row (i j : β) :
    ∫ r : β → ℂ, r i * conj (r j) * eR r =
      if i = j then (Real.pi : ℂ) ^ Fintype.card β else 0 := by
  simp_rw [row_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun k : β => hf (k = i) (k = j))]
  simp_rw [integral_hf]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [h]

variable {d : ℕ}

def rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) (r : β → ℂ) : ℂ :=
  (∑ i, r i * G i a) * conj (∑ j, r j * G j c) * eR r

theorem rowF_eq (G : Matrix β (Fin d) ℂ) (a c : Fin d) (r : β → ℂ) :
    rowF G a c r = ∑ i, ∑ j, (G i a * conj (G j c)) * (r i * conj (r j) * eR r) := by
  rw [rowF, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

theorem integrable_rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) : Integrable (rowF G a c) := by
  have : rowF G a c = fun r => ∑ i, ∑ j, (G i a * conj (G j c)) * (r i * conj (r j) * eR r) :=
    funext (rowF_eq G a c)
  rw [this]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (integrable_row i j).const_mul _

theorem integral_rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) :
    ∫ r, rowF G a c r = (Real.pi : ℂ) ^ Fintype.card β * (G.conjTranspose * G) c a := by
  simp_rw [rowF_eq]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (integrable_row i j).const_mul _]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (integrable_row i j).const_mul _]
  simp only [integral_const_mul, integral_row, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  simp only [Complex.star_def]
  ring

theorem det_expand (G : Matrix β (Fin d) ℂ) (C : Fin d → β → ℂ) :
    ((Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) * ‖(Matrix.of C * G).det‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
          ∏ k, rowF G (σ k) (τ k) (C k) := by
  set M := Matrix.of C * G with hMdef
  have hM : ∀ k a, M k a = ∑ i, C k i * G i a := fun k a => by
    simp [hMdef, Matrix.mul_apply]
  have hd : M.det = ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, M k (σ k) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    simp [Matrix.transpose_apply]
  have hc : conj M.det =
      ∑ τ : Equiv.Perm (Fin d), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, conj (M k (τ k)) := by
    rw [hd, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, map_prod]
    simp
  have hn : ((‖M.det‖ ^ 2 : ℝ) : ℂ) = M.det * conj M.det := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hE : ((Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) : ℝ) : ℂ) = ∏ k, eR (C k) := by
    simp only [eR]
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    push_cast
    rfl
  have hp : ∀ σ τ : Equiv.Perm (Fin d), ∏ k, rowF G (σ k) (τ k) (C k) =
      (∏ k, M k (σ k)) * (∏ k, conj (M k (τ k))) * ∏ k, eR (C k) := fun σ τ => by
    simp only [rowF, Finset.prod_mul_distrib, hM]
  rw [Complex.ofReal_mul, hn, hE]
  conv_lhs => rw [hc]; rw [hd]
  simp only [hp]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

theorem perm_sum (p : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
          ∏ k, (p * A (τ k) (σ k)) = p ^ d * (d.factorial : ℂ) * A.det := by
  have h1 : ∀ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
        ∏ k, (p * A (τ k) (σ k)) = p ^ d * A.det := fun σ => by
    have h2 := Matrix.det_permute' σ A
    rw [Matrix.det_apply'] at h2
    simp only [Matrix.submatrix_apply, id] at h2
    have hs : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    calc _ = ((Equiv.Perm.sign σ : ℤ) : ℂ) * p ^ d *
          ∑ τ : Equiv.Perm (Fin d), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, A (τ k) (σ k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          ring
      _ = p ^ d * A.det := by
          rw [h2]
          linear_combination (p ^ d * A.det) * hs
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integrable_prod_rowF (G : Matrix β (Fin d) ℂ) (σ τ : Equiv.Perm (Fin d)) :
    Integrable (fun C : Fin d → β → ℂ => ∏ k, rowF G (σ k) (τ k) (C k)) := by
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun k : Fin d => rowF G (σ k) (τ k)) (μ := fun _ => volume)
    fun k => integrable_rowF G _ _

theorem integral_prod_rowF (G : Matrix β (Fin d) ℂ) (σ τ : Equiv.Perm (Fin d)) :
    ∫ C : Fin d → β → ℂ, ∏ k, rowF G (σ k) (τ k) (C k) =
      ∏ k, ((Real.pi : ℂ) ^ Fintype.card β * (G.conjTranspose * G) (τ k) (σ k)) := by
  rw [integral_fintype_prod_volume_eq_prod (fun k : Fin d => rowF G (σ k) (τ k))]
  simp_rw [integral_rowF]

def fR (G : Matrix β (Fin d) ℂ) (C : Fin d → β → ℂ) : ℝ :=
  Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) * ‖(Matrix.of C * G).det‖ ^ 2

theorem integrable_fR_complex (G : Matrix β (Fin d) ℂ) :
    Integrable (fun C => ((fR G C : ℝ) : ℂ)) := by
  simp_rw [fR, det_expand]
  exact integrable_finset_sum _ fun σ _ => integrable_finset_sum _ fun τ _ =>
    (integrable_prod_rowF G σ τ).const_mul _

theorem integral_fR_complex (G : Matrix β (Fin d) ℂ) :
    ∫ C, ((fR G C : ℝ) : ℂ) = ((Real.pi : ℂ) ^ Fintype.card β) ^ d * (d.factorial : ℂ) *
      (G.conjTranspose * G).det := by
  simp_rw [fR, det_expand]
  rw [integral_finset_sum _ fun σ _ => integrable_finset_sum _ fun τ _ =>
    (integrable_prod_rowF G σ τ).const_mul _]
  rw [← perm_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finset_sum _ fun τ _ => (integrable_prod_rowF G σ τ).const_mul _]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_prod_rowF]

end GlobalTheory.CompanionTheory.FSCrofton.GaussDet

open GlobalTheory.CompanionTheory.FSCrofton.GaussDet in

theorem GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq (d : ℕ) (β : Type) [Fintype β] [DecidableEq β]
    (G : Matrix β (Fin d) ℂ) :
    ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (‖(Matrix.of C * G).det‖ ^ 2) =
      ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
        (G.conjTranspose * G).det.re) := by
  have hint : Integrable (fR G) := by
    have := (integrable_fR_complex G).re
    simpa using this
  have hnn : 0 ≤ᵐ[volume] fR G := ae_of_all _ fun C => by
    simp only [fR, Pi.zero_apply]
    positivity
  have hval : ∫ C, fR G C = Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) *
      (G.conjTranspose * G).det.re := by
    have h := integral_fR_complex G
    rw [integral_complex_ofReal] at h
    have h2 := congrArg Complex.re h
    rw [Complex.ofReal_re] at h2
    rw [h2, pow_mul' ]
    have : ((Real.pi : ℂ) ^ Fintype.card β) ^ d * (d.factorial : ℂ) =
        (((Real.pi ^ Fintype.card β) ^ d * (d.factorial : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [this, Complex.re_ofReal_mul]
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine lintegral_congr fun C => ?_
  rw [gW, fR, ENNReal.ofReal_mul (Real.exp_pos _).le]
