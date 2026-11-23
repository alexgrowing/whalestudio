import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixGreenValue
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrix_green_value : ∀ v : ReciprocityTheory.L2DbarEstimates.V 1, 2 * diagVal (extTrace (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => (Matrix.fromBlocks (Matrix.of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0)) (Matrix.of fun _ _ => w 0) (Matrix.of fun _ _ => starRingEnd ℂ (w 0)) 1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)) v) (EuclideanSpace.single 0 1) = 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
  first | exact @GlobalTheory.TautDensity.density_eq | exact GlobalTheory.TautDensity.density_eq | (intros; apply GlobalTheory.TautDensity.density_eq <;> assumption)
