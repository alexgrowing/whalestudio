import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absHalf_conjugatePlace_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ x : E, absHalf u (algebraMap E (u.adicCompletion E) x) = absHalf w (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) := by
  first | exact @GlobalTheory.BCT.AbsHalfConj.absHalf_conjPl | exact GlobalTheory.BCT.AbsHalfConj.absHalf_conjPl | (intros; apply GlobalTheory.BCT.AbsHalfConj.absHalf_conjPl <;> assumption)
