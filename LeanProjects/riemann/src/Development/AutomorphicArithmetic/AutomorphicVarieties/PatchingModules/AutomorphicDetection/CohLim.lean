import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.TaylorWilesFirstConditionAtLimitOfGroupCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.TaylorWilesSecondConditionAtLimitOfGroupConditio
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.FirstCohomologyBoundOfBoundaryBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondCohomologyBoundOfBoundaryBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.KoszulThreeOfDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SubgroupQuot

open UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem cohLim : CohLim := by
  intro l _ L G0 T Λ n x k al D0 _ hT he h1 h2
  have hPh : TopFG Λ.Ph := by
    obtain ⟨s, hs⟩ := Λ.fg
    exact ⟨s, s.finite_toSet, (topGen_iff _).2 hs⟩
  have hG : TopFG Λ.G.Γ := (TopFG.subgroup_quot Λ.Ph hPh).2 _ Λ.πo Λ.πo_cont Λ.πo_surj
  exact ⟨firstCohomologyBound_of_boundaryBound l L _ _ Λ.h n x k D0 hG (taylorWiles_first_condition_at_limit_of_group_condition l L G0 T Λ n x k D0 h1), secondCohomologyBound_of_boundaryBound l L _ _ Λ.h n x k hG (taylorWiles_second_condition_at_limit_of_group_condition l L G0 T Λ n x k h2),
    koszulThree_of_det l L G0 T Λ n x k al hT he⟩

end UpperTheory.V.Pa
