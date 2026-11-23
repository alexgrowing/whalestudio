import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeLowerBoundTopLatticeOffHypersurface
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slopeLowerBound_topLattice_offHypersurface : SlopeBound := by
  first | exact @GlobalTheory.HSShort.SlopeTop.slopeBound | exact GlobalTheory.HSShort.SlopeTop.slopeBound | (intros; apply GlobalTheory.HSShort.SlopeTop.slopeBound <;> assumption)
