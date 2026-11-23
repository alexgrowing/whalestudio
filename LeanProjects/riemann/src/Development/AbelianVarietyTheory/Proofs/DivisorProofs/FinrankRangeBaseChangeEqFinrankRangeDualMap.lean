import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDualAndRangeDualMapBaseChange
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem finrank_range_baseChange_eq_dualMap_and_finrank_dual :
    ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (M₁ : Type) [AddCommGroup M₁] [Module O M₁] [Module.Free O M₁] [Module.Finite O M₁] (M₂ : Type) [AddCommGroup M₂] [Module O M₂] [Module.Free O M₂] [Module.Finite O M₂] (f : M₁ →ₗ[O] M₂), Module.finrank K (LinearMap.range (f.baseChange K)) = Module.finrank K (LinearMap.range (f.dualMap.baseChange K)) ∧ Module.finrank K (K ⊗[O] M₁) = Module.finrank K (K ⊗[O] Module.Dual O M₁) := by
  intro O _ K _ _ M₁ _ _ _ _ M₂ _ _ _ _ f
  obtain ⟨h1, h2⟩ := GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M₁ M₂ K f
  exact ⟨h2.symm, h1.symm⟩

end GlobalTheory.AbCoh
