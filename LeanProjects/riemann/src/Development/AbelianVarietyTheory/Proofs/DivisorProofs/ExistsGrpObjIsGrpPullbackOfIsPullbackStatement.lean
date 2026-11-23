import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s' : Over (Sp R')), IsGrpPullback (Over.mk s' : Over (Sp R')) A (spMap σ) φ ∧ (IsAbelianScheme A → IsAbelianScheme (Over.mk s' : Over (Sp R'))) ∧ ∀ g, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g s' := by
  first | exact @GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback | exact GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback | (intros; apply GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback <;> assumption)
