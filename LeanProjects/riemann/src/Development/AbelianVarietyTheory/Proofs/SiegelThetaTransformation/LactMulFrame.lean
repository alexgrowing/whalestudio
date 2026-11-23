import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

namespace GlobalTheory.LeftActionFrameMul

open ReciprocityTheory.ChartRestriction.G.FD

theorem lact_mul_frame {E : Type} [Field E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (γ' γ : GL (Fin r) E) (x : Frame Ψ r) : lact (γ' * γ) x = lact γ' (lact γ x) := by
  funext τ

  show ((γ' * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

end GlobalTheory.LeftActionFrameMul
