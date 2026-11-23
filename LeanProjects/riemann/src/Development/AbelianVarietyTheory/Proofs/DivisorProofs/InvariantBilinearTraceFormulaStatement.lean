import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantBilinearTraceFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_bilinear_trace_formula : ∀ (r : ℕ) (B : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] ℂ) (μ : ℂ), (∀ U : Matrix (Fin r) (Fin r) ℂ, Uᴴ * U = 1 → ∀ F F', B (Uᴴ * F * U) (Uᴴ * F' * U) = B F F') → (∀ a b c d : Fin r, B (Matrix.single a b 1) (Matrix.single c d 1) = B (Matrix.single c b 1) (Matrix.single a d 1)) → (∀ F, B 1 F = μ * F.trace) → ∀ F F', B F F' = μ / (r + 1) * (F.trace * F'.trace + (F * F').trace) := by
  first | exact @GlobalTheory.UnitInvBilin.eq_trace_form | exact GlobalTheory.UnitInvBilin.eq_trace_form | (intros; apply GlobalTheory.UnitInvBilin.eq_trace_form <;> assumption)
