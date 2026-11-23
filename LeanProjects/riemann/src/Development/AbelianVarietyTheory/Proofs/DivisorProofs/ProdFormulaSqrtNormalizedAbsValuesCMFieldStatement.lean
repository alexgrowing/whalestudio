import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFormulaSqrtNormalizedAbsValuesCMField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodFormula_sqrt_normalizedAbsValues_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E), x ≠ 0 → (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)).Finite ∧ (∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x)) * ∏ v : InfinitePlace E, (‖v.embedding x‖ : ℂ) = 1 := by
  first | exact @GlobalTheory.ProdForm.absHalf_prodFormula | exact GlobalTheory.ProdForm.absHalf_prodFormula | (intros; apply GlobalTheory.ProdForm.absHalf_prodFormula <;> assumption)
