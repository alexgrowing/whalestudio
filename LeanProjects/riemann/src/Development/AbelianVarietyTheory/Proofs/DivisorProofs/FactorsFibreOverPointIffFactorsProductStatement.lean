import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsFibreOverPointIffFactorsProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factors_fibreOverPoint_iff_factors_product : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T) (Y : Over (Sp V)) (x : Y ⟶ GlobalTheory.TwistFlat.bc A φ), (∃ y : Y ⟶ GlobalTheory.TwistFlat.ker A φ h, y ≫ GlobalTheory.TwistFlat.kerι A φ h = x) ↔ ∃ z : GlobalTheory.TwistFlat.up φ Y ⟶ H, z ≫ h = lift (GlobalTheory.TwistFlat.upa φ x) (GlobalTheory.TwistFlat.upt φ Y) := by
  first | exact @GlobalTheory.TwistFlat.factor_ker_iff | exact GlobalTheory.TwistFlat.factor_ker_iff | (intros; apply GlobalTheory.TwistFlat.factor_ker_iff <;> assumption)
