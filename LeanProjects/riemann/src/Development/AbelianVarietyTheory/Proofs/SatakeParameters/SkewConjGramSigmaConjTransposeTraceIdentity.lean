import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
open Matrix

namespace GlobalTheory

theorem skewConj_cT_mul_and_trace :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, σ (σ x) = x) →
  ∀ (n r : ℕ) (JS : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) → (∀ k j, σ (Γ k j) = - Γ j k) →
  Formalism.UG.cT σ (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) ∧
  ∀ (n' : ℕ) (JT : GL (Fin n') L) (y : Matrix (Fin n') (Fin n) L),
    Matrix.trace ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) =
      Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) := by
  intro L _ _ σ hσ n r JS M Γ hJ hΓ
  have hmul : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L),
      Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
    intro a b c A B
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcc : Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
    ext i j
    simp [Formalism.UG.cT, hσ]
  have hJ' : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := by
    ext i j
    simp [Formalism.UG.cT, hJ]
  have hΓ' : Formalism.UG.cT σ Γ = -Γ := by
    ext i j
    simp [Formalism.UG.cT, hΓ]
  refine ⟨?_, ?_⟩
  · rw [hmul, hmul, hmul, hcc, hJ', hΓ']
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  · intro n' JT y
    rw [hmul, Matrix.mul_assoc (M * Γ * Formalism.UG.cT σ M), Units.mul_inv, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm M]
    simp only [Matrix.mul_assoc]

end GlobalTheory
