import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GelfandGraevCharacterGLnNormAndReciprocity
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandGraevCharacterGLn_norm_and_reciprocity : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n → wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) ∧ ∀ χ : Gn g n → ℂ, IsClass χ → ip χ (gg ψ n) = wh ψ χ := by
  first | exact @GlobalTheory.GLq.GGNorm.gg_norm | exact GlobalTheory.GLq.GGNorm.gg_norm | (intros; apply GlobalTheory.GLq.GGNorm.gg_norm <;> assumption)
