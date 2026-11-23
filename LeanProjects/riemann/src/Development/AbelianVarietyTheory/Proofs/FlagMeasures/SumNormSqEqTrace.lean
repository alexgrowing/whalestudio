import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA.FrobNorm

variable {k r : ℕ}

theorem sum_normSq_eq_trace (g : B.Mat k r) :
    (∑ i, ∑ j, Complex.normSq (g i j)) = (trace (gᴴ * g)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem gN_unitary_mul {κ : B.Mat k r} (g : B.Mat k r) (hκ : κᴴ * κ = 1) : B.gN (κ * g) = B.gN g := by
  have hsq : (κ * g)ᴴ * (κ * g) = gᴴ * g := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ κ g, hκ, Matrix.one_mul]
  simp only [B.gN]
  rw [sum_normSq_eq_trace, sum_normSq_eq_trace, hsq]

theorem gN_conjTranspose (g : B.Mat k r) : B.gN gᴴ = B.gN g := by
  simp only [B.gN, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  rw [Finset.sum_comm]

theorem gN_mul_unitary {κ : B.Mat k r} (g : B.Mat k r) (hκ : κ * κᴴ = 1) : B.gN (g * κ) = B.gN g := by
  have hκ' : κᴴᴴ * κᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hκ
  rw [← gN_conjTranspose (g * κ), Matrix.conjTranspose_mul, gN_unitary_mul gᴴ hκ', gN_conjTranspose]

open scoped Matrix.Norms.Frobenius in
theorem gN_eq_norm (g : B.Mat k r) : B.gN g = ‖g‖ := by
  rw [Matrix.frobenius_norm_def, B.gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.rpow_two, Complex.normSq_eq_norm_sq]

open scoped Matrix.Norms.Frobenius in
theorem gN_mul_le (x y : B.Mat k r) : B.gN (x * y) ≤ B.gN x * B.gN y := by
  simpa only [gN_eq_norm] using Matrix.frobenius_norm_mul x y

theorem left_inv {g : B.Mat k r} (hg : g ∈ B.GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, GBasic.Hpk_sq]

theorem inv_eq {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have h := left_inv hg
  exact Matrix.inv_eq_left_inv h

theorem gN_inv {g : B.Mat k r} (hg : g ∈ B.GV k r) : B.gN g⁻¹ = B.gN g := by
  have h1 : (Hpk k r)ᴴ * Hpk k r = 1 := by rw [GBasic.Hpk_herm, GBasic.Hpk_sq]
  have h2 : Hpk k r * (Hpk k r)ᴴ = 1 := by rw [GBasic.Hpk_herm, GBasic.Hpk_sq]
  rw [inv_eq hg, gN_mul_unitary _ h2, gN_unitary_mul _ h1, gN_conjTranspose]

end GlobalTheory.ThA.FrobNorm
