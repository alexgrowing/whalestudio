import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.torus_dual_frame_rows_eigen : ∀ (R : Type) [CommRing R] (m r : ℕ) (X Y : Matrix (Fin m) (Fin r) R) (X' Y' : Matrix (Fin r) (Fin m) R) (d e : Matrix (Fin r) (Fin r) R) (A B : Matrix (Fin m) (Fin m) R), X' * X = 0 → Y' * Y = 0 → X' * Y = 1 → Y' * X = 1 → d * e = 1 → e * d = 1 → A * X = X * d → A * Y = Y * e → A * (1 - X * Y' - Y * X') = 1 - X * Y' - Y * X' → A * B = 1 → Y' * B = e * Y' ∧ X' * B = d * X' ∧ (1 - X * Y' - Y * X') * B = 1 - X * Y' - Y * X' := by
  intro R _ m r X Y X' Y' d e A B hX'X hY'Y hX'Y hY'X hde hed hAX hAY hAP hAB
  obtain ⟨P, hP⟩ : ∃ P, P = 1 - X * Y' - Y * X' := ⟨_, rfl⟩
  rw [← hP] at hAP ⊢
  have hsum : X * Y' + Y * X' + P = 1 := by rw [hP]; abel
  have hY'P : Y' * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hY'X, hY'Y, Matrix.one_mul, Matrix.zero_mul, sub_self, zero_sub, neg_zero]
  have hX'P : X' * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hX'X, hX'Y, Matrix.one_mul, Matrix.zero_mul, sub_zero, sub_self]
  have hPX : P * X = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      hY'X, hX'X, Matrix.mul_one, Matrix.mul_zero, sub_self, sub_zero]
  have hPY : P * Y = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      hY'Y, hX'Y, Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  have hPP : P * P = P := by
    have h1 : P * P = P * (1 - X * Y' - Y * X') := by rw [← hP]
    rw [h1, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hPX, hPY, Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]
  have hA : A = X * d * Y' + Y * e * X' + P := by
    calc A = A * (X * Y' + Y * X' + P) := by rw [hsum, Matrix.mul_one]
      _ = X * d * Y' + Y * e * X' + P := by
        rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY, hAP]
  have hY'A : Y' * A = d * Y' := by
    rw [hA, Matrix.mul_add, Matrix.mul_add, hY'P, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hY'X, hY'Y, Matrix.one_mul, Matrix.zero_mul,
      Matrix.zero_mul, add_zero, add_zero]
  have hX'A : X' * A = e * X' := by
    rw [hA, Matrix.mul_add, Matrix.mul_add, hX'P, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX'X, hX'Y, Matrix.one_mul, Matrix.zero_mul,
      Matrix.zero_mul, zero_add, add_zero]
  have hPA : P * A = P := by
    rw [hA, Matrix.mul_add, Matrix.mul_add, hPP, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPX, hPY, Matrix.zero_mul, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.zero_mul, zero_add, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · calc Y' * B = (e * d) * (Y' * B) := by rw [hed, Matrix.one_mul]
      _ = e * ((Y' * A) * B) := by rw [hY'A, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = e * Y' := by rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
  · calc X' * B = (d * e) * (X' * B) := by rw [hde, Matrix.one_mul]
      _ = d * ((X' * A) * B) := by rw [hX'A, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = d * X' := by rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
  · calc P * B = (P * A) * B := by rw [hPA]
      _ = P := by rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
