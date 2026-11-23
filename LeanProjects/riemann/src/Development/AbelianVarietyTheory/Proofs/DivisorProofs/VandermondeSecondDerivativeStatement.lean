import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeSecondDerivative
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
theorem _root_.GlobalTheory.T.vandermonde_second_derivative : ∀ r : ℕ, ∃ κ : ℝ, ∀ a b : Fin r, apolar ((∑ i : Fin r, MvPolynomial.X (some i) ^ 2) * ∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)) : MvPolynomial (Option (Fin r)) ℝ) (MvPolynomial.X (some a) * (MvPolynomial.X (some b) * ∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)))) = κ * ((if a = b then (r : ℝ) + 1 else 0) - 1) := by
  first | exact @GlobalTheory.VdmApolarPair.apolar_psq_vdm | exact GlobalTheory.VdmApolarPair.apolar_psq_vdm | (intros; apply GlobalTheory.VdmApolarPair.apolar_psq_vdm <;> assumption)
