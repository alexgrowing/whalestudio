import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasureInvertibleIntegralMatrices
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_invertible_integral_matrices : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ r : ℕ, ∀ (dx : Measure (Matrix (Fin r) (Fin r) F)), dx.IsAddLeftInvariant → dx (intMat O r r) = 1 → MeasurableSet (Jset (GLint O r)) ∧ dx (Jset (GLint O r)) = ENNReal.ofReal (qE q 1 r) := by
  first | exact @GlobalTheory.CompanionTheory.QL.VolK.vol_GLint | exact GlobalTheory.CompanionTheory.QL.VolK.vol_GLint | (intros; apply GlobalTheory.CompanionTheory.QL.VolK.vol_GLint <;> assumption)
