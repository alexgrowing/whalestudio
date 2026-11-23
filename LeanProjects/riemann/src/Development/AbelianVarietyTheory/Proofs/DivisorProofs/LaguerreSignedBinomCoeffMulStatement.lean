import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreSignedBinomCoeffMul
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laguerreSignedBinomCoeff_mul : ∀ k n m j : ℕ, j ≤ m → m ≤ n → rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by
  first | exact @GlobalTheory.HilbFam.rco_mul_rco | exact GlobalTheory.HilbFam.rco_mul_rco | (intros; apply GlobalTheory.HilbFam.rco_mul_rco <;> assumption)
