import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormOfHomogeneousPrimeKrullDim
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chowForm_of_homogeneous_prime_krullDim : ∀ (K : Type) [Field K] (N D : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ) → ∃ (δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f := by
  first | exact @GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq | exact GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq | (intros; apply GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq <;> assumption)
