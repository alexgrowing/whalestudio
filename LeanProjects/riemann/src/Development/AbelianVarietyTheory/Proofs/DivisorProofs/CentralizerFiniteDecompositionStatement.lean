import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerFiniteDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_finite_decomposition : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ → ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ x : Gr G r, (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, x⁻¹ * inclG G r γ * x = e * k) → ∃ t : Gr G r, t * inclG G r γ = inclG G r γ * t ∧ ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, x = t * d * k := by
  first | (exact @GlobalTheory.OrbFinP.orbit_fin_p) | (exact GlobalTheory.OrbFinP.orbit_fin_p) | (intros; apply GlobalTheory.OrbFinP.orbit_fin_p <;> assumption)
