import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaQuotientCharMulInvEqOne
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_quotient_char_mul_inv_eq_one : ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ), q ≠ 0 → (q : 𝓞 E) ∈ P.asIdeal → ∀ (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n : ℕ), ∀ g ∈ LocE.JQ P q kj n 0, LocE.lamQB ξ kj n g.toLinearMap * LocE.lamQB ξ kj n (g⁻¹).toLinearMap = 1 := by
  first | exact @GlobalTheory.TwistRowType.lamQB_mul_inv | exact GlobalTheory.TwistRowType.lamQB_mul_inv | (intros; apply GlobalTheory.TwistRowType.lamQB_mul_inv <;> assumption)
