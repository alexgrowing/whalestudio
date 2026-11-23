import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem trace_eq_of_intertwined_by_quasi_inverse (A : Type) [CommRing A] [IsDomain A] (h : ℕ) (μ : A)
    (F G X Y : Matrix (Fin h) (Fin h) A) (hμ : μ ≠ 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) (hFX : F * X = Y * F) :
    F * G = μ • (1 : Matrix (Fin h) (Fin h) A) ∧ X * G = G * Y ∧ Y.trace = X.trace := by
  have hdet : G.det * F.det = μ ^ h := by
    rw [← Matrix.det_mul, hGF, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hF : F.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero h hμ hdet.symm
  have hFG : F * G = μ • (1 : Matrix (Fin h) (Fin h) A) := by
    have h1 : (F * G - μ • (1 : Matrix (Fin h) (Fin h) A)) * F = 0 := by
      rw [sub_mul, Matrix.mul_assoc, hGF, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : F.det • (F * G - μ • (1 : Matrix (Fin h) (Fin h) A)) = 0 := by
      have := congrArg (· * F.adjugate) h1
      simp only [Matrix.zero_mul] at this
      rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at this
      exact this
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hF
    · exact sub_eq_zero.mp h3
  have hXG : X * G = G * Y := by
    have e : μ • (X * G) = μ • (G * Y) := by
      calc μ • (X * G) = (G * F) * X * G := by
              rw [hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
        _ = G * (Y * (F * G)) := by
              rw [Matrix.mul_assoc G F X, hFX, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
                Matrix.mul_assoc (G * Y)]
        _ = μ • (G * Y) := by
              rw [hFG, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
    exact smul_right_injective _ hμ e
  refine ⟨hFG, hXG, ?_⟩
  have e : μ * Y.trace = μ * X.trace := by
    calc μ * Y.trace = (μ • Y).trace := by rw [Matrix.trace_smul, smul_eq_mul]
      _ = ((F * G) * Y).trace := by rw [hFG, Matrix.smul_mul, Matrix.one_mul]
      _ = (G * (Y * F)).trace := by
            rw [Matrix.mul_assoc, Matrix.trace_mul_comm F (G * Y), Matrix.mul_assoc]
      _ = ((G * F) * X).trace := by rw [← hFX, Matrix.mul_assoc]
      _ = (μ • X).trace := by rw [hGF, Matrix.smul_mul, Matrix.one_mul]
      _ = μ * X.trace := by rw [Matrix.trace_smul, smul_eq_mul]
  exact mul_left_cancel₀ hμ e

end GlobalTheory
