import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturation
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHomogeneous_and_hilbertPoly_eq_of_prime_in_saturation : ∀ (K : Type) [Field K] (N : ℕ) (I Q : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) → Q.IsPrime → I ≤ Q → (∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) → (∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q) ∧ GlobalTheory.idealHilbertPoly Q = GlobalTheory.idealHilbertPoly I := by
  first | exact @GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq | exact GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq | (intros; apply GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq <;> assumption)
