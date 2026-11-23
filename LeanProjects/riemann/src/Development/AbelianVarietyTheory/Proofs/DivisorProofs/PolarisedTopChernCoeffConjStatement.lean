import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffConj
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_conj : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (P : Matrix r r ℂ), IsUnit P.det → mixTop (fun i a b => P⁻¹ * K i a b * P) = mixTop K := by
  first | exact @GlobalTheory.GoodTop.mixTop_conj | exact GlobalTheory.GoodTop.mixTop_conj | (intros; apply GlobalTheory.GoodTop.mixTop_conj <;> assumption)
