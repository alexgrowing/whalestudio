import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChebyshevPsiProgressionRelativeError
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chebyshevPsiProgression_relative_error : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧ ∀ (M : ℕ) [NeZero M] (b : ℕ) (θ : ℤ) (β u : ℝ), 3 ≤ M → Nat.Coprime b M → ExcData c₁ M b θ β → (M : ℝ) ^ c₂ ≤ u → |(M.totient : ℝ) * psiAP M b u - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log M) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β)) := by
  first | exact @GlobalTheory.Lin.PsiRel.psiAP_relative | exact GlobalTheory.Lin.PsiRel.psiAP_relative | (intros; apply GlobalTheory.Lin.PsiRel.psiAP_relative <;> assumption)
