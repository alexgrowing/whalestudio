import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleSpecProdAbelianCohomologousSumMul
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_spec_prod_abelian_cohomologous_sum_mul : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (D : Type) [CommRing D] [Algebra R D] (u : Fn1 (SpAlg R D ⊗ B)), IsCoc (whole _) u → ∃ (n : ℕ) (d : Fin n → D) (β : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), Cohom (whole _) u (sumMul d fun i ↦ fv (β i)) := by
  first | exact @GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian | exact GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian | (intros; apply GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian <;> assumption)
