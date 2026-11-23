import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOneFormsIsBaseChangeTangentRep
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_oneForms_isBaseChange_tangentRep : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ∀ (W : Type) [AddCommGroup W] [Module R W], TanRep A W → ∃ j : W →ₗ[R] GlobForm A.hom, ∀ T : AffOp A.left, ∃ e : W →ₗ[R] Ω[(OAff A.hom).obj T⁄R], (∀ w, e w = (j w).1 T) ∧ IsBaseChange ((OAff A.hom).obj T) e := by
  first | exact @GlobalTheory.TanForms.exists_globForm_isBaseChange | exact GlobalTheory.TanForms.exists_globForm_isBaseChange | (intros; apply GlobalTheory.TanForms.exists_globForm_isBaseChange <;> assumption)
