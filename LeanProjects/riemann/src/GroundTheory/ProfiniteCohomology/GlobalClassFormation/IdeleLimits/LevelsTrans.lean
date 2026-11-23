import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Levels
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  FiniteSubfield IdeleLimit

noncomputable section

variable {K F E M : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (K ≤ M)] [Fact (F ≤ E)]
  [Fact (E ≤ M)] [Fact (F ≤ M)] [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]
  [M.1.fixingSubgroup.Normal]

theorem levelRestrict_levelRestrict (τ : M.1 ≃ₐ[K.1] M.1) :
    levelRestrict K F E (levelRestrict K E M τ) = levelRestrict K F M τ := by
  ext x
  have h1 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := F) (E := E)
    (levelRestrict K E M τ) x)
  have h2 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := E) (E := M) τ
    (algebraMap F.1 E.1 x))
  have h3 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := F) (E := M) τ x)
  exact h1.trans (h2.trans h3.symm)

set_option maxHeartbeats 2000000 in

theorem levelTransition_comp_levelTransition (n : ℕ) :
    levelTransition K F E n ≫ levelTransition K E M n = levelTransition K F M n := by
  unfold levelTransition cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  congr 1
  ext m x : 3
  apply Subtype.ext
  funext g
  change Additive.ofMul (ideleMap (Fact.out : E ≤ M) (ideleMap (Fact.out : F ≤ E)
      ((x.1 fun i => levelRestrict K F E (levelRestrict K E M (g i))).toMul))) =
    Additive.ofMul (ideleMap (Fact.out : F ≤ M) ((x.1 fun i => levelRestrict K F M (g i)).toMul))
  have hfun : (fun i => levelRestrict K F E (levelRestrict K E M (g i))) =
      fun i => levelRestrict K F M (g i) := funext fun i => levelRestrict_levelRestrict (g i)
  refine (congrArg Additive.ofMul (ideleMap_ideleMap (Fact.out : F ≤ E) (Fact.out : E ≤ M) _)).trans ?_
  rw [hfun]

end

end GroundTheory.ProfCoh
