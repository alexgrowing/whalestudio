import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorCoeff_conjugateSeries : ∀ (D : D7) (N N' : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D N N' → ℂ), Differentiable ℂ (fnConj D M ρ G) → fnConj D M ρ G ≠ 0 → (∀ α, taylor D (fnConj D M ρ G) α = cj M ρ (taylor D G α)) ∧ (CoefIn D G M → ∀ (n : D.what₂.Tau → ℕ) (T : Tup D N N' n), GL3Theta.applyAt0 D (minorPol D T) G ∈ M ∧ cj M ρ (GL3Theta.applyAt0 D (minorPol D T) G) = GL3Theta.applyAt0 D (minorPol D T) (fnConj D M ρ G)) := by
  first | exact @GlobalTheory.ConjSeries.taylor_fnConj | exact GlobalTheory.ConjSeries.taylor_fnConj | (intros; apply GlobalTheory.ConjSeries.taylor_fnConj <;> assumption)
