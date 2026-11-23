import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieSequenceExactAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallApplyHodgePrimitiveEqZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem surjective_of_isCan_field : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K], (p : K) = 0 → ∀ (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p K) (t : G.TorsionTower A) (ψ : PrimitiveSubmodule A →ₗ[K] G.omega), (∀ c : PrimitiveSubmodule A, IsCan t c.1 (G.rigOfOmega (ψ c))) → Function.Surjective ψ := by
  intro hH p _ K _ hp A _ g hA hg G t ψ hψ
  have hL : LieExact A :=
    GlobalTheory.LieHodge.lieExact_of_crystallineLift_hodgeDeRham GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH K A g hA hg
  have hx := GlobalTheory.T.eq_zero_of_forall_apply_hodgePrimitive_eq_zero p K 1 (by rw [pow_one]; exact hp) A hA hL G t ψ hψ
  rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
  intro x hx0
  exact hx x fun c ↦ by simpa using LinearMap.congr_fun hx0 c

end GlobalTheory.PtExt
