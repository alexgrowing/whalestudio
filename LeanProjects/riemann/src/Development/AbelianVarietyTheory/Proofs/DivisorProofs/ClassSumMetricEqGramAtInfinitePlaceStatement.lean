import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumMetricEqGramAtInfinitePlace
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSumMetric_eq_gram_at_infinitePlace : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (T : Formalism.L2.Col.GSD K) (h : T.Ok), T.Rat → ∀ (v : InfinitePlace K) (φ : T.EqFun), T.ipAt h v φ.1 φ.1 = star (fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) ⬝ᵥ ((T.toCSD h).H.map v.embedding *ᵥ fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) := by
  first | exact @GlobalTheory.ClassSumCoord.ipAt_eq_gram | exact GlobalTheory.ClassSumCoord.ipAt_eq_gram | (intros; apply GlobalTheory.ClassSumCoord.ipAt_eq_gram <;> assumption)
