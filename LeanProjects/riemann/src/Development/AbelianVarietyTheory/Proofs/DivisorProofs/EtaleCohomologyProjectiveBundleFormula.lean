import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleCohomologyProjectiveBundleFormula
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
theorem _root_.GlobalTheory.T.etaleCohomology_projectiveBundle_formula : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), ∀ {N : ℕ} (V : sch.obj U ⟶ ofCat (glCat N)), Inv q (sch.obj U) → ∀ n i : ℤ, Function.Bijective fun a : ∀ j : Fin N, Ht q (sch.obj U) (n - 2 * (j : ℕ)) (i - (j : ℕ)) => ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j)) (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i) :=
  @UpperTheory.Cb.etaleCohomology_projectiveBundle_formula
