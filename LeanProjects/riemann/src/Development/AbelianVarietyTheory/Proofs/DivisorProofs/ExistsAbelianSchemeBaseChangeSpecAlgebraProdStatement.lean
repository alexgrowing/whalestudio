import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeSpecAlgebraProd
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
theorem _root_.GlobalTheory.T.exists_abelianScheme_baseChange_spec_algebra_prod : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∃ (B' : Over (Sp D)) (_ : GrpObj B') (π : B'.left ⟶ B.left) (q : B'.left ⟶ (SpAlg R D ⊗ B).left), IsGrpPullback B' B (spMap (algebraMap R D)) π ∧ IsAbelianScheme B' ∧ SmoothOfRelativeDimension g B'.hom ∧ IsIso q ∧ q ≫ (fst (SpAlg R D) B).left = B'.hom ∧ q ≫ (snd (SpAlg R D) B).left = π := by
  first | exact @GlobalTheory.exists_baseChange_spAlg_prod | exact GlobalTheory.exists_baseChange_spAlg_prod | (intros; apply GlobalTheory.exists_baseChange_spAlg_prod <;> assumption)
