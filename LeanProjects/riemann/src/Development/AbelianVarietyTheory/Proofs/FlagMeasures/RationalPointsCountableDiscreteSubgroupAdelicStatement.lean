import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelic
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoints_countable_discrete_subgroup_adelic : ∀ (I : AutInst), (∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset) ∧ I.GFset.Countable ∧ ∀ C : Set I.GA, IsCompact C → (I.GFset ∩ C).Finite := by
  first | exact @GlobalTheory.RatDiscrete.subgroup_countable_discrete | exact GlobalTheory.RatDiscrete.subgroup_countable_discrete | (intros; apply GlobalTheory.RatDiscrete.subgroup_countable_discrete <;> assumption)
