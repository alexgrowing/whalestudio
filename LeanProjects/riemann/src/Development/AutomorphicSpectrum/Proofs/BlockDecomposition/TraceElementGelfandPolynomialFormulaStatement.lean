import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementGelfandPolynomialFormula
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_element_gelfand_polynomial_formula : ∀ (m : ℕ) (χ : Fin (m + 1) → ℂ) (N : ℕ), ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))).comp (Polynomial.X + 1) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2)))) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) = GlobalTheory.Dec.gelfVal χ N := by
  first | exact @GlobalTheory.CompanionTheory.GelfRec.gelfVal_newton | exact GlobalTheory.CompanionTheory.GelfRec.gelfVal_newton | (intros; apply GlobalTheory.CompanionTheory.GelfRec.gelfVal_newton <;> assumption)
