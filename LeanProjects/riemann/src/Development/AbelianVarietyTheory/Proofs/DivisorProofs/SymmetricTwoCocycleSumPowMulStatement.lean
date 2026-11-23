import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleSumPowMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_two_cocycle_sum_pow_mul : ∀ (Γ D : Type) [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D), (∀ x y, c x y = c y x) → (∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) → ∀ (n : ℕ) (x y : Γ), ∑ i ∈ Finset.range n, c ((x * y) ^ i) (x * y) + n • c x y = ∑ i ∈ Finset.range n, c (x ^ i) x + ∑ i ∈ Finset.range n, c (y ^ i) y + c (x ^ n) (y ^ n) - c 1 1 := by
  first | exact @GlobalTheory.TwoCocycle.sum_pow_mul | exact GlobalTheory.TwoCocycle.sum_pow_mul | (intros; apply GlobalTheory.TwoCocycle.sum_pow_mul <;> assumption)
