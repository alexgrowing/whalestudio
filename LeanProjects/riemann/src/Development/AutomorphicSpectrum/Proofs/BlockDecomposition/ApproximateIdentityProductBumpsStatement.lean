import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApproximateIdentityProductBumps
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximate_identity_product_bumps : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [T2Space A] [Fintype ι] (e : G ≃ₜ+ (ι → A)) (ρ : ℕ → A → ℝ), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ ∀ y, 0 ≤ ρ k y) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : A)).smallSets → (∀ k, Continuous (fun T : G => ∏ i, ρ k (e T i)) ∧ HasCompactSupport (fun T : G => ∏ i, ρ k (e T i)) ∧ ∀ T : G, 0 ≤ ∏ i, ρ k (e T i)) ∧ Filter.Tendsto (fun k => tsupport (fun T : G => ∏ i, ρ k (e T i))) Filter.atTop (nhds (0 : G)).smallSets := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.prod_coordinate_bumps | exact GlobalTheory.CompanionTheory.BigCell.prod_coordinate_bumps | (intros; apply GlobalTheory.CompanionTheory.BigCell.prod_coordinate_bumps <;> assumption)
