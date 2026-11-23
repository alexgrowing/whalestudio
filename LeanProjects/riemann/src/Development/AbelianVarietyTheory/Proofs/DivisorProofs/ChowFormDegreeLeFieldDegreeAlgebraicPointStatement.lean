import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormDegreeLeFieldDegreeAlgebraicPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chowForm_degree_le_field_degree_algebraic_point : ∀ (K : Type) [Field K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → IsChowFormInt (coneIdeal K y) 0 δ f → δ ≤ Module.finrank K (IntermediateField.adjoin K (Set.range y)) := by
  first | exact @GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt | exact GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt | (intros; apply GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt <;> assumption)
