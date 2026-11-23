import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.EigBoxL
open UpperTheory.V.Z.Desc.V0

theorem UpperTheory.V.Z.Desc.V0.eigBoxE :
    EigBoxE := by
  intro L _ _ n V _ S G H W W' X _ _ _ _ _ _ _ _ ρ κ π f hf hint m K₁ K₂ τ₀ b φ μ a N
  exact eigBoxL ρ κ π f hf hint m K₁ K₂ τ₀ b φ μ a N
