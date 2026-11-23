import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnUnitTransvections
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_on_unit_transvections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E), ξ ∈ X.Λ → ξ ≠ 0 → herm X.Gm ξ ξ = 0 → ∃ u : 𝓞 E, u ≠ 0 ∧ cc (u : E) = u ∧ ∀ t : E, cc t = t → IsIntegral ℤ t → ∀ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm ξ (X.m * (u * t) * X.κ0) → φ γ = 1 := by
  first | exact @GlobalTheory.UnipKill.killsScaled | exact GlobalTheory.UnipKill.killsScaled | (intros; apply GlobalTheory.UnipKill.killsScaled <;> assumption)
