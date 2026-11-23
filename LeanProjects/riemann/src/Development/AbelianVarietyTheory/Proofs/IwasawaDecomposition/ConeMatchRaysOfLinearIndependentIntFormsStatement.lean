import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysOfLinearIndependentIntForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coneMatch_rays_of_linearIndependent_intForms : ∀ {X : Type} [AddCommGroup X] {k m : ℕ} (p : Fin k → LinearMap.BilinForm ℤ X) (δ : Fin m → LinearMap.BilinForm ℤ X),
  LinearIndependent ℤ p → LinearIndependent ℤ δ →
  ∀ (t : Fin k → ℝ) (c : Fin m → ℝ), (∀ i, 0 < t i) → (∀ j, 0 ≤ c j) → ∑ i, t i • toReal (p i) = ∑ j, c j • toReal (δ j) →
    (∀ i, InRCone δ (p i)) → (∀ j, 0 < c j → InRCone p (δ j)) →
    (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.cone_match_rays | exact GlobalTheory.PolFan.cone_match_rays | (intros; apply GlobalTheory.PolFan.cone_match_rays <;> assumption)
