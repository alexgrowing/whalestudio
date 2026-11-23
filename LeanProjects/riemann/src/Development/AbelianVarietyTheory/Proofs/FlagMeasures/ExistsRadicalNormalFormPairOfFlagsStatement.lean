import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRadicalNormalFormPairOfFlags
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_radical_normalForm_pair_of_flags : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (p : Point ℂ (r + 1)), TwoFl k r z z' g₀ → ZhatO k r z z' g₀ = ptMat p → ∃ p₁ p₀ : PPar k r, pOf k r p₀ *ᵥ z' = z' ∧ IsNormal k r (fun a => blockIdx p.1 a.val) (pOf k r p₁ * g₀ * (pOf k r p₀)⁻¹) ∧ Zr k r (pOf k r p₁ * g₀ * (pOf k r p₀)⁻¹) = Zr k r g₀ ∧ ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r := by
  first | exact @GlobalTheory.Amp.NormalEx.normal_form | exact GlobalTheory.Amp.NormalEx.normal_form | (intros; apply GlobalTheory.Amp.NormalEx.normal_form <;> assumption)
