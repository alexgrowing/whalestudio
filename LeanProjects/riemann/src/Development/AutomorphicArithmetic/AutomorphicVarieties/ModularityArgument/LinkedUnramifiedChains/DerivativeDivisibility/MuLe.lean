import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime

open Polynomial TensorProduct

theorem UpperTheory.V.J.muLe :
    UpperTheory.V.J.MuLe := by
  intro O Λ B K _ _ _ _ _ _ _ _ lam M _ _ _ _ _ hs y t
  unfold UpperTheory.V.J.mu
  refine (Submodule.finrank_mono (iInf_le _ t)).trans ?_
  rw [LinearMap.finrank_maxGenEigenspace_eq, LinearMap.charpoly_baseChange]
  rfl
