import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_centralizer_decomposition : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ → ∀ δ z : Gr G r, IsNrm G r γ δ z → ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ t : Gr G r, t * nrmG (sigG G r) r δ = nrmG (sigG G r) r δ * t → (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, t⁻¹ * δ * sigG G r t = e * k) → ∃ u ∈ GlobalTheory.BCT.twCent (sigG G r) δ, ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, t = u * d * k := by
  first | (exact @GlobalTheory.TwFin.main) | (exact GlobalTheory.TwFin.main) | (intros; apply GlobalTheory.TwFin.main <;> assumption)
