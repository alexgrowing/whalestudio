import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysAfterDroppingZeroCoords
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullAddInjective
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_match_rays_after_dropping_zero_coords : ∀ {X : Type} [AddCommGroup X] {m₀ : ℕ} (p : Fin m₀ → LinearMap.BilinForm ℤ X) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) →
  LinearIndependent ℤ (fun i : {i // 0 < t i} => p i) →
  ∀ β : LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), LinearIndependent ℤ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  (∀ i, 0 < t i → InRCone δ (p i)) →
  (∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧ toReal (δ j) = ∑ i, a i • toReal (p i)) →
  (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.cone_match_rays_of_nonneg | exact GlobalTheory.PolFan.cone_match_rays_of_nonneg | (intros; apply GlobalTheory.PolFan.cone_match_rays_of_nonneg <;> assumption)
