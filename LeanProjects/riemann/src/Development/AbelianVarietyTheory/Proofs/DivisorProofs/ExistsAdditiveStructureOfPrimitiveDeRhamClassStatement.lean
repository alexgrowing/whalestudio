import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClass
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR A → ∃ g : Fn2 A, IsAdd (fv f) g := by
  first | exact @GlobalTheory.PtExt.exists_isAdd_of_mem_primDR | exact GlobalTheory.PtExt.exists_isAdd_of_mem_primDR | (intros; apply GlobalTheory.PtExt.exists_isAdd_of_mem_primDR <;> assumption)
