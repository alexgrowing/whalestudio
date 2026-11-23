import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEq
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
theorem _root_.GlobalTheory.T.baseChangePull_sum_mul_pointValue_eq : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R)) (B' : Over (Sp D)) (q : B'.left ⟶ (SpAlg R D ⊗ B).left) (w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D)) (π : B'.left ⟶ B.left), q ≫ (fst (SpAlg R D) B).left = B'.hom → q ≫ (snd (SpAlg R D) B).left = π → ∀ (mB : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 D) (B'.hom ≫ 𝟙 _) (algebraMap R D) π) (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), bcPull w (sumMul d fun i ↦ fv (β i)) = fv (∑ i, d i • mB.coef.pullbackOneCocycle (β i)) := by
  first | exact @GlobalTheory.PtExt.bcPull_sumMul_fv | exact GlobalTheory.PtExt.bcPull_sumMul_fv | (intros; apply GlobalTheory.PtExt.bcPull_sumMul_fv <;> assumption)
