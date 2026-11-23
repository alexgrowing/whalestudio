import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.GradedDegreeZeroIsLocal

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem hJ_sum_sum' {n : ℕ} (ε : Fin n → Bool) {ι : Type} [Fintype ι] (a b : ι → ℂ) (x y : ι → Fin n → ℂ) :
    hJ ε (∑ j, a j • x j) (∑ k, b k • y k) = ∑ j, ∑ k, conj (a j) * b k * hJ ε (x j) (y k) := by
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_sum, Matrix.mulVec_smul, star_sum, star_smul,
    dotProduct_sum, sum_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hJ_adj {n : ℕ} {ε : Fin n → Bool} (s : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat s *ᵥ y) = hJ ε (uMat s⁻¹ *ᵥ x) y := by
  have hU : (uMat s)ᴴ * Formalism.REAL.Jm ε * uMat s = Formalism.REAL.Jm ε := s.2
  have hinv : uMat s * uMat s⁻¹ = 1 := by
    simp [Formalism.MainNotions.S.uMat]
  have hJc : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    rw [Pi.star_apply]
    split_ifs <;> simp
  have h1 : (uMat s)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat s⁻¹ := by
    calc (uMat s)ᴴ * Formalism.REAL.Jm ε = (uMat s)ᴴ * Formalism.REAL.Jm ε * (uMat s * uMat s⁻¹) := by
          rw [hinv, Matrix.mul_one]
      _ = Formalism.REAL.Jm ε * uMat s⁻¹ := by rw [← Matrix.mul_assoc, hU]
  have key : (uMat s⁻¹)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat s := by
    have h2 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJc] at h2
    exact h2.symm
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, key]

theorem zAct : ZAct := by
  intro n r ε f f' s s' g P P' hP hP'
  ext a b
  have hu : uMat (s * g * s'⁻¹) = uMat s * uMat g * uMat s'⁻¹ := by
    simp [Formalism.MainNotions.S.uMat]
  have hw : uMat g *ᵥ (uMat s'⁻¹ *ᵥ f' b) = ∑ d, P' d b • (uMat g *ᵥ f' d) := by
    rw [hP' b, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  rw [Formalism.L2.SG.RealObj.Zhat, hu, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hJ_adj, hP a, hw,
    hJ_sum_sum']
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.L2.SG.RealObj.Zhat, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [starRingEnd_apply]
  ring

theorem upMat_lower {r : ℕ} (y : UC r) (a b : Fin (r + 1)) (h : b < a) : upMat y a b = 0 := by
  have h1 : a ≠ b := ne_of_gt h
  have h2 : ¬ a < b := not_lt.mpr h.le
  simp [upMat, h1, h2]

theorem upMat_diag {r : ℕ} (y : UC r) (a : Fin (r + 1)) : upMat y a a = 1 := by
  simp [upMat]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
