import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentative

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_reduced_orbit_representative : ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) → Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by
  first | exact @GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | exact GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | (intros; apply GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate <;> assumption)
