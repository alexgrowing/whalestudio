import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfPrimitiveBalancedFormSameRealRay
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (x y : LinearMap.BilinForm ℤ X)
    (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), IsPrim bar (⟨x, hx⟩ : balForms bar X) →
    IsPrim bar (⟨y, hy⟩ : balForms bar X) → ∀ b : ℝ, 0 < b → toReal x = b • toReal y → x = y := by
  first | exact @GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul | exact GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul | (intros; apply GlobalTheory.PolFan.SmoothEnd.eq_of_isPrim_of_toReal_eq_smul <;> assumption)
