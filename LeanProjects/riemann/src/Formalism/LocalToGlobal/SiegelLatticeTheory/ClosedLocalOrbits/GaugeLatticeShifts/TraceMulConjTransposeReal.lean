import Formalism.LocalRingCardinality.DataCD

open Matrix

noncomputable section

namespace Formalism.MainNotions.S.Gauge.Cd

variable {P Q : ℕ}

local notation "ι" => Fin P ⊕ Fin Q

theorem jpq_sq : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  unfold Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp

theorem jpq_conjTranspose : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Jpq
  rw [Matrix.fromBlocks_conjTranspose]
  simp

theorem trace_mul_conjTranspose_real {a b : Matrix ι ι ℂ} (ha : a ∈ Formalism.BasicNotions.lieU P Q) (hb : b ∈ Formalism.BasicNotions.lieU P Q) :
    star (Matrix.trace (a * bᴴ)) = Matrix.trace (a * bᴴ) := by
  have hb' : bᴴ = -(Formalism.UG.Jpq P Q * b * Formalism.UG.Jpq P Q) := by
    have h : bᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * b = 0 := hb
    have h2 : bᴴ * Formalism.UG.Jpq P Q = -(Formalism.UG.Jpq P Q * b) := eq_neg_of_add_eq_zero_left h
    calc bᴴ = bᴴ * Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q := by rw [Matrix.mul_assoc, jpq_sq, Matrix.mul_one]
      _ = -(Formalism.UG.Jpq P Q * b * Formalism.UG.Jpq P Q) := by rw [h2, Matrix.neg_mul]
  have ha' : aᴴ = -(Formalism.UG.Jpq P Q * a * Formalism.UG.Jpq P Q) := by
    have h : aᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * a = 0 := ha
    have h2 : aᴴ * Formalism.UG.Jpq P Q = -(Formalism.UG.Jpq P Q * a) := eq_neg_of_add_eq_zero_left h
    calc aᴴ = aᴴ * Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q := by rw [Matrix.mul_assoc, jpq_sq, Matrix.mul_one]
      _ = -(Formalism.UG.Jpq P Q * a * Formalism.UG.Jpq P Q) := by rw [h2, Matrix.neg_mul]
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ha', hb']
  simp only [Matrix.mul_neg, Matrix.trace_neg]
  congr 1
  calc (b * (Formalism.UG.Jpq P Q * a * Formalism.UG.Jpq P Q)).trace
      = ((b * Formalism.UG.Jpq P Q) * (a * Formalism.UG.Jpq P Q)).trace := by simp only [Matrix.mul_assoc]
    _ = ((a * Formalism.UG.Jpq P Q) * (b * Formalism.UG.Jpq P Q)).trace := Matrix.trace_mul_comm _ _
    _ = (a * (Formalism.UG.Jpq P Q * b * Formalism.UG.Jpq P Q)).trace := by simp only [Matrix.mul_assoc]

def hs2 (Z : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (Z i j)

theorem hilbert_schmidt_eq_re_trace (Z : Matrix ι ι ℂ) : hs2 Z = (Matrix.trace (Z * Zᴴ)).re := by
  unfold hs2
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem hilbert_schmidt_add_I_smul {a b : Matrix ι ι ℂ} (ha : a ∈ Formalism.BasicNotions.lieU P Q) (hb : b ∈ Formalism.BasicNotions.lieU P Q) :
    hs2 (a + Complex.I • b) = hs2 a + hs2 b := by
  rw [hilbert_schmidt_eq_re_trace, hilbert_schmidt_eq_re_trace, hilbert_schmidt_eq_re_trace]
  have hT := trace_mul_conjTranspose_real ha hb
  have hT' : (Matrix.trace (a * bᴴ)).im = 0 := by
    have := congrArg Complex.im hT
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, smul_eq_mul, Complex.star_def, Complex.conj_I]
  have hba : Matrix.trace (b * aᴴ) = star (Matrix.trace (a * bᴴ)) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [hba, hT]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, hT']
  rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, hT']
  ring

end Formalism.MainNotions.S.Gauge.Cd
