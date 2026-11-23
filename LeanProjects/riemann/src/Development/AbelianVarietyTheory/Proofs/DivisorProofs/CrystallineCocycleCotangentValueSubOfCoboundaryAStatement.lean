import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueSubOfCoboundaryA
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotVal_sub_eq_dUnit_of_d0_eq_sub : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (D : Type) [CommRing D] [Bialgebra R D] (y : Pt X D) (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (k : C0 (O (dp0 R) (X.hom ≫ 𝟙 _))), d0 _ k = f.1 - f'.1 → cotVal f y - cotVal f' y = dUnit R (show D from k (trivAt y)) := by
  first | exact @GlobalTheory.PtExt.crystallineCocycleCotangentValue_sub_of_coboundary | exact GlobalTheory.PtExt.crystallineCocycleCotangentValue_sub_of_coboundary | (intros; apply GlobalTheory.PtExt.crystallineCocycleCotangentValue_sub_of_coboundary <;> assumption)
