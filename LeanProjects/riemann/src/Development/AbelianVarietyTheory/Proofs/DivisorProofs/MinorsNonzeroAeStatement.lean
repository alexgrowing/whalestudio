import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsNonzeroAe
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
theorem _root_.GlobalTheory.T.minors_nonzero_ae : ∀ (m : ℕ) (g : Matrix (Fin m) (Fin m) ℂ), IsUnit g.det → ∀ᵐ x : Low m → ℂ, ∀ l : Fin (m + 1), ((g * uni x).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
  first | exact @GlobalTheory.FlagCell.ae_leading_minors_mul_uni_ne_zero | exact GlobalTheory.FlagCell.ae_leading_minors_mul_uni_ne_zero | (intros; apply GlobalTheory.FlagCell.ae_leading_minors_mul_uni_ne_zero <;> assumption)
