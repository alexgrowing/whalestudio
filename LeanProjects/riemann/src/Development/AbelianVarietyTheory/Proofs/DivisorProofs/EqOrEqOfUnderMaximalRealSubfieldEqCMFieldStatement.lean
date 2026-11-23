import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_or_eq_of_under_maximalRealSubfield_eq_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u u' : Pl E), u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → u'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → u' = w ∨ u' = u := by
  first | exact @GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq | exact GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq | (intros; apply GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq <;> assumption)
