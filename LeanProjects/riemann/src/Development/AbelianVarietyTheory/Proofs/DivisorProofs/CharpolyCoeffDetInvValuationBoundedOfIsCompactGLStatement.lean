import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffDetInvValuationBoundedOfIsCompactGL
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_coeff_det_inv_valuation_bounded_of_isCompact_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (C : Set (GLw n w)), IsCompact C → ∃ γ : WithZero (Multiplicative ℤ), ∀ y ∈ C, (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ γ := by
  first | exact @GlobalTheory.BCT.charpoly_det_bounded_of_isCompact | exact GlobalTheory.BCT.charpoly_det_bounded_of_isCompact | (intros; apply GlobalTheory.BCT.charpoly_det_bounded_of_isCompact <;> assumption)
