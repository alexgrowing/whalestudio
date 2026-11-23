import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesExistsMarkedFormInCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_exists_marked_form_in_cone : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) (c : FormFamily O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m : ℕ} (δ₀ : Fin m → LinearMap.BilinForm ℤ X₀) (v : LinearMap.BilinForm ℤ X₀) (t : Fin m → ℝ),
  v ∈ balForms bar X₀ → v ≠ 0 → (∀ y, 0 ≤ v y y) → c.Carries δ₀ → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), c.Carries δ →
    ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ (OrbMark.orbFun O w0 v).evalZ β = 1 ∧ InRCone δ β := by
  first | exact @GlobalTheory.PolFan.carries_exists_marked | exact GlobalTheory.PolFan.carries_exists_marked | (intros; apply GlobalTheory.PolFan.carries_exists_marked <;> assumption)
