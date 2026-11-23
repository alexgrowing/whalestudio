import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactIsometryLieAlgebraBound
import Mathlib
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_isometry_lie_algebra_bound : ∀ (n : ℕ) (A R : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool), Aᴴ = A →
    Rᴴ * A * R = Matrix.diagonal (fun i => if ε i then (1 : ℂ) else -1) →
    ∀ v : Fin n → ℂ, star v ⬝ᵥ A *ᵥ v = 0 →
    ∀ (T : Type) [TopologicalSpace T] (S : Set T), IsCompact S →
    ∀ m : T → Matrix (Fin n) (Fin n) ℂ, ContinuousOn m S → (∀ t ∈ S, (m t)ᴴ * A * m t = A) →
    ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * A + A * X = 0 →
      ∃ (e e' : ℕ) (Yb : Fin e → Matrix (Fin n) (Fin n) ℂ) (l : Fin e → ℂ) (Zb : Fin e' → Matrix (Fin n) (Fin n) ℂ) (C : ℝ),
        (∀ j, (Yb j)ᴴ * A + A * Yb j = 0 ∧ Yb j *ᵥ v = l j • v) ∧
        (∀ j, (Zb j)ᴴ * A + A * Zb j = 0 ∧ (R⁻¹ * Zb j * R)ᴴ = -(R⁻¹ * Zb j * R)) ∧
        ∀ t ∈ S, ∃ (c : Fin e → ℝ) (c' : Fin e' → ℝ), (∀ j, |c j| ≤ C) ∧ (∀ j, |c' j| ≤ C) ∧
          X = ∑ j, c j • ((m t)⁻¹ * Yb j * m t) + ∑ j, c' j • Zb j := by
  first | exact @GlobalTheory.UniformLieDecomp.decomp | exact GlobalTheory.UniformLieDecomp.decomp | (intros; apply GlobalTheory.UniformLieDecomp.decomp <;> assumption)
