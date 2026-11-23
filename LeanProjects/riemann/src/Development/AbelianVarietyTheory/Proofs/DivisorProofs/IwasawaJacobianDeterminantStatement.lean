import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaJacobianDeterminant
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
theorem _root_.GlobalTheory.T.iwasawa_jacobian_determinant : ∀ (m : ℕ) (g : Matrix (Fin m) (Fin m) ℂ) (φ : (Low m → ℂ) → Low m → ℂ) (B : (Low m → ℂ) → Matrix (Fin m) (Fin m) ℂ) (x : Low m → ℂ), (∀ᶠ y in 𝓝 x, (B y).BlockTriangular id ∧ g * uni y = uni (φ y) * B y) → IsUnit (B x).det → DifferentiableAt ℂ φ x → (∀ a c, DifferentiableAt ℂ (fun y => B y a c) x) → |((fderiv ℂ φ x).restrictScalars ℝ).det| = ∏ s : Low m, ‖B x s.1.1 s.1.1 / B x s.1.2 s.1.2‖ ^ 2 := by
  first | exact @GlobalTheory.FlagFibre.abs_det_fderiv_flag | exact GlobalTheory.FlagFibre.abs_det_fderiv_flag | (intros; apply GlobalTheory.FlagFibre.abs_det_fderiv_flag <;> assumption)
