import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSeriesSummableShifted
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_series_summable_shifted : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (Γ Q P : Subgroup G) (ξ lam : G → ℝ) (t : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, lam (γ * x) = lam x) →
    PositivityTheory.RgEis.Conv Γ P (fun x => lam x + t * ξ x) → ∀ g : G,
    Summable fun r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ => Real.exp (t * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos (Γ ⊓ Q) P lam (PositivityTheory.RgEis.rep r * g) := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.cross_stage_pos | exact GlobalTheory.CompanionTheory.RgEis.cross_stage_pos | (intros; apply GlobalTheory.CompanionTheory.RgEis.cross_stage_pos <;> assumption)
