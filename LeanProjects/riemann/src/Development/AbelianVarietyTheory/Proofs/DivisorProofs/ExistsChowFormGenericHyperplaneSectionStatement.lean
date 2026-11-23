import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormGenericHyperplaneSection
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chowForm_generic_hyperplane_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)) (D δ : ℕ) (f : MvPolynomial (Fin (D + 1 + 1) × Fin N) K), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → IsChowFormInt P (D + 1) δ f → ∃ f' : MvPolynomial (Fin (D + 1) × Fin N) L, IsChowFormInt (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)}) D δ f' := by
  first | exact @GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section | exact GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section | (intros; apply GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section <;> assumption)
