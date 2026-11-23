import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipTool

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Unip

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]

private theorem mul_eq_one_comm_of_mul_eq_one {G G' : Matrix ι ι K} (h : G * G' = 1) : G' * G = 1 :=
  mul_eq_one_comm.mp h

theorem conj_pow {G G' Z : Matrix ι ι K} (h : G * G' = 1) (j : ℕ) : G' * Z ^ j * G = (G' * Z * G) ^ j := by
  have hG : G' * G = 1 := mul_eq_one_comm_of_mul_eq_one h
  induction j with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hG]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G G', h, Matrix.one_mul]

theorem conj_geo {G G' Z : Matrix ι ι K} (h : G * G' = 1) (N : ℕ) : G' * geo N Z * G = geo N (G' * Z * G) := by
  unfold geo
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => conj_pow h j

theorem conj_cay [Invertible (2 : K)] {G G' Z : Matrix ι ι K} (h : G * G' = 1) (N : ℕ) :
    G' * cay N Z * G = cay N (G' * Z * G) := by
  have hG : G' * G = 1 := mul_eq_one_comm_of_mul_eq_one h
  have e1 : G' * ((⅟2 : K) • Z) * G = (⅟2 : K) • (G' * Z * G) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  unfold cay
  rw [← e1, ← conj_geo h, mul_add, add_mul, Matrix.mul_one, hG]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G G', h, Matrix.one_mul]

theorem conj_sharp {J J' G G' A : Matrix ι ι K} (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J') (hJ : J' * J = 1) (hJ' : J * J' = 1)
    (hG : Gᴴ * J * G = J) (h : G * G' = 1) : G' * sharp J J' A * G = sharp J J' (G' * A * G) := by
  have key : G' = J' * Gᴴ * J := by
    calc G' = (J' * (Gᴴ * J * G)) * G' := by rw [hG, hJ, Matrix.one_mul]
      _ = J' * Gᴴ * J * (G * G') := by simp only [Matrix.mul_assoc]
      _ = J' * Gᴴ * J := by rw [h, Matrix.mul_one]
  have key' : G'ᴴ = J * (G * J') := by
    rw [key]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJh, hJ'h, Matrix.mul_assoc]
  unfold sharp
  rw [conjTranspose_mul, conjTranspose_mul, key']
  rw [key]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc J J', hJ', Matrix.one_mul, hJ, Matrix.mul_one]

theorem conj_proj [Invertible (2 : K)] {J J' G G' A : Matrix ι ι K} (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J')
    (hJ : J' * J = 1) (hJ' : J * J' = 1) (hG : Gᴴ * J * G = J) (h : G * G' = 1) :
    G' * proj J J' A * G = proj J J' (G' * A * G) := by
  unfold proj
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, conj_sharp hJh hJ'h hJ hJ' hG h]

end Formalism.L2.SG.Pf.Unip
