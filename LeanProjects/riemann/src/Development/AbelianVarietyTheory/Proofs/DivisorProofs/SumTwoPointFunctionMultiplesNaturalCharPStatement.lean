import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwoPointFunctionMultiplesNaturalCharP
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumTwoPointFunction_multiples_natural_charP : ∀ (p : ℕ) (R : Type) [CommRing R], (p : R) = 0 → ∀ (A : Over (Sp R)) [GrpObj A] (f : Fn1 A) (g : Fn2 A), IsAdd f g → ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D), chi p g D' (spOver φ ≫ x) - φ (chi p g D x) = f D D' φ (x ^ p) - f D D' φ 1 := by
  first | exact @GlobalTheory.PtExt.chi_natural | exact GlobalTheory.PtExt.chi_natural | (intros; apply GlobalTheory.PtExt.chi_natural <;> assumption)
