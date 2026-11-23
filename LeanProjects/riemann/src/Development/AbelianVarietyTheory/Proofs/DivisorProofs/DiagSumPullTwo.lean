import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem diagSum_pullTwo : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] [CommRing D'] [Bialgebra R D'] [Coalgebra.IsCocomm R D'] (f : D →ₐc[R] D')
    (m : ℕ) (c : D ⊗[R] D), f (diagSum R D m c) = diagSum R D' m (pullbackTwo f c) := by
  intro R _ D D' _ _ _ _ _ _ f m c
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [diagSum_tmul, pullbackTwo, TensorProduct.map_tmul, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mulBy]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end GlobalTheory.PtExt
