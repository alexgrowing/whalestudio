import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivZeroEqLaguerreDerivativePolynomialV
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_zero_eq_laguerreDerivativePolynomialValue : ∀ (k n : ℕ) (c y : ℂ), iteratedDeriv n (fun z : ℂ ↦ (1 + z * c)⁻¹ ^ k * Complex.exp (y * z / (1 + z * c))) 0 = lag k n c y := by
  first | exact @GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag | exact GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag | (intros; apply GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag <;> assumption)
