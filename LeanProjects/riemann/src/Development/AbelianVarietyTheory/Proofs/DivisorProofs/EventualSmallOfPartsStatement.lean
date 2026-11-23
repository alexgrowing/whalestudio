import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualSmallOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventual_small_of_parts : ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜), AtAll PSeeEx 𝒜 σ → AtAll PPA 𝒜 σ → EvWC (fun _ => True) Small 𝒜 σ := by
  first | exact @GlobalTheory.Fc.Ind.small_along | exact GlobalTheory.Fc.Ind.small_along | (intros; apply GlobalTheory.Fc.Ind.small_along <;> assumption)
