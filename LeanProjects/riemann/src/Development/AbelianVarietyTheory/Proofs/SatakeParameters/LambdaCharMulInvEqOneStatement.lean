import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharMulInvEqOne
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_char_mul_inv_eq_one : ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ), q ≠ 0 → (q : 𝓞 E) ∈ P.asIdeal → ∀ (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r t j n : ℕ), r + j * t ≤ n → ∀ g ∈ LocE.JG P q k₀ r t n 0, LocE.lamGB q ψ₀ χ k₀ r t j n 0 g.toLinearMap * LocE.lamGB q ψ₀ χ k₀ r t j n 0 (g⁻¹).toLinearMap = 1 := by
  first | exact @GlobalTheory.lamGB_mul_lamGB_inv | exact GlobalTheory.lamGB_mul_lamGB_inv | (intros; apply GlobalTheory.lamGB_mul_lamGB_inv <;> assumption)
