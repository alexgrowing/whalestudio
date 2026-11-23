import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegralOfCommuteSeparableReduction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integral_of_commute_separable_reduction : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ) (P₀ : (w.adicCompletionIntegers E)[X]),
    IsCoprime P₀ (derivative P₀) →
    ∀ (A s : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, A i j ∈ w.adicCompletionIntegers E) →
    A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → Commute s A →
    (∃ B : WithZero (Multiplicative ℤ), ∀ (k : ℕ) (i j : Fin n), Valued.v ((s ^ k) i j) ≤ B) →
    ∀ i j, s i j ∈ w.adicCompletionIntegers E := by
  first | exact @GlobalTheory.IntMatSep.integral_of_commute_sep | exact GlobalTheory.IntMatSep.integral_of_commute_sep | (intros; apply GlobalTheory.IntMatSep.integral_of_commute_sep <;> assumption)
