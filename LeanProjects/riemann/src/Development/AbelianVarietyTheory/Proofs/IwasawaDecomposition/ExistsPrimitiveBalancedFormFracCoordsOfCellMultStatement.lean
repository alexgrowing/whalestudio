import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveBalancedFormFracCoordsOfCellMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitiveBalancedForm_fracCoords_of_cellMult : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → 2 ≤ M →
  ∃ (v : LinearMap.BilinForm ℤ X) (hv : v ∈ balForms bar X), IsPrim bar (⟨v, hv⟩ : balForms bar X) ∧ (∀ y, 0 ≤ v y y) ∧
    ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i ∧ t i < 1) ∧ toReal v = ∑ i, t i • toReal (δ i) := by
  first | exact @GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac | exact GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac | (intros; apply GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac <;> assumption)
