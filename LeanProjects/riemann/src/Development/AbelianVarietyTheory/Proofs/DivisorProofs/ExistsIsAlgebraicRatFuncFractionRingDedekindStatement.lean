import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgebraicRatFuncFractionRingDedekind
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind : ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∃ _ : Algebra (RatFunc k) (FractionRing B), Algebra.IsAlgebraic (RatFunc k) (FractionRing B) := by
  first | (exact @GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc) | (exact GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc) | (intros; apply GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc  <;> assumption)
