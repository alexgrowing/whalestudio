import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem chi_natural : ∀ (p : ℕ) (R : Type) [CommRing R], (p : R) = 0 → ∀ (A : Over (Sp R)) [GrpObj A] (f : Fn1 A) (g : Fn2 A), IsAdd f g → ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D), chi p g D' (spOver φ ≫ x) - φ (chi p g D x) = f D D' φ (x ^ p) - f D D' φ 1 := by
  intro p R _ hp A _ f g hg D _ _ D' _ _ φ x
  have hp' : (p : D') = 0 := by
    rw [← map_natCast (algebraMap R D') p, hp, map_zero]
  unfold chi
  rw [map_sum, ← Finset.sum_sub_distrib]
  have h : ∀ i ∈ Finset.range p, g D' ((spOver φ ≫ x) ^ i) (spOver φ ≫ x) - φ (g D (x ^ i) x) =
      (f D D' φ (x ^ (i + 1)) - f D D' φ (x ^ i)) - f D D' φ x := by
    intro i _
    rw [← MonObj.comp_pow, hg D D' φ (x ^ i) x, pow_succ]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ f D D' φ (x ^ i)) p,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, hp', zero_mul, sub_zero, pow_zero]

end GlobalTheory.PtExt
