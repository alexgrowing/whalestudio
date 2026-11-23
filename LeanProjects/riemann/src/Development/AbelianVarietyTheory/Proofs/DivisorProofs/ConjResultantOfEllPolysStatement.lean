import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjResultantOfEllPolys
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_resultant_of_ell_polys : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (P₁ P₂ : E[X]), P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCMField.complexConj E (resultant P₁ P₂) * (((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a) = (-1) ^ (a * b) * resultant P₁ P₂ := by
  first | exact @GlobalTheory.ResConj.conj_resultant | exact GlobalTheory.ResConj.conj_resultant | (intros; apply GlobalTheory.ResConj.conj_resultant <;> assumption)
