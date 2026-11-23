import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
import Development.AutomorphicSpectrum.Proofs.JetProofs.ScalarOnComplement

open Matrix

namespace GlobalTheory.CompanionTheory.Dblock.CompFrame

theorem exists_comp_frame : ∀ {n D : ℕ} (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin D) ℂ),
    Cᴴ * C = 1 → Cᴴ * Formalism.REAL.Jm ε * C = 0 →
    ∃ (m : ℕ) (R : Matrix (Fin n) (Fin m) ℂ) (ε' : Fin m → Bool),
      Rᴴ * R = 1 ∧ Formalism.REAL.Jm ε * R = R * Formalism.REAL.Jm ε' ∧ Cᴴ * R = 0 ∧
      C * Cᴴ + Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε + R * Rᴴ = 1 := by
  intro n D ε C h1 h2
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := GlobalTheory.CompanionTheory.HCSide.CentreNone.Jm_herm ε
  generalize hJ : Formalism.REAL.Jm ε = J at *
  have hAA : C * Cᴴ * (C * Cᴴ) = C * Cᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Cᴴ, h1, Matrix.one_mul]
  have hAB : C * Cᴴ * (J * C * Cᴴ * J) = 0 := by
    have e : C * Cᴴ * (J * C * Cᴴ * J) = C * (Cᴴ * J * C) * Cᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]; simp
  have hBA : J * C * Cᴴ * J * (C * Cᴴ) = 0 := by
    have e : J * C * Cᴴ * J * (C * Cᴴ) = J * C * (Cᴴ * J * C) * Cᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]; simp
  have hBB : J * C * Cᴴ * J * (J * C * Cᴴ * J) = J * C * Cᴴ * J := by
    have e : J * C * Cᴴ * J * (J * C * Cᴴ * J) = J * C * (Cᴴ * (J * J) * C) * Cᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e, hJJ, Matrix.mul_one, h1, Matrix.mul_one]
  have hPh : (1 - C * Cᴴ - J * C * Cᴴ * J)ᴴ = 1 - C * Cᴴ - J * C * Cᴴ * J := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose, hJh,
      Matrix.mul_assoc]
  have hPP : (1 - C * Cᴴ - J * C * Cᴴ * J) * (1 - C * Cᴴ - J * C * Cᴴ * J) =
      1 - C * Cᴴ - J * C * Cᴴ * J := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hAA, hAB, hBA, hBB]
    abel
  have hPJ : J * (1 - C * Cᴴ - J * C * Cᴴ * J) = (1 - C * Cᴴ - J * C * Cᴴ * J) * J := by
    have e1 : J * (J * C * Cᴴ * J) = C * Cᴴ * J := by
      simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    have e2 : J * C * Cᴴ * J * J = J * (C * Cᴴ) := by
      rw [Matrix.mul_assoc _ J J, hJJ, Matrix.mul_one, Matrix.mul_assoc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2]
    abel
  subst hJ
  obtain ⟨m, ε', R, r1, r2, r3⟩ := GlobalTheory.CompanionTheory.HCSide.CentreNone.exists_frame_J hPh hPP hPJ
  refine ⟨m, R, ε', r1, r3, ?_, ?_⟩
  · have hCP : Cᴴ * (1 - C * Cᴴ - Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) = 0 := by
      have e : Cᴴ * (Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) =
          (Cᴴ * Formalism.REAL.Jm ε * C) * Cᴴ * Formalism.REAL.Jm ε := by
        simp only [Matrix.mul_assoc]
      rw [Matrix.mul_sub, Matrix.mul_sub, e, h2, ← Matrix.mul_assoc, h1]
      simp
    have e : R = (1 - C * Cᴴ - Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) * R := by
      rw [← r2, Matrix.mul_assoc, r1, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, hCP, Matrix.zero_mul]
  · rw [r2]; abel

end GlobalTheory.CompanionTheory.Dblock.CompFrame
