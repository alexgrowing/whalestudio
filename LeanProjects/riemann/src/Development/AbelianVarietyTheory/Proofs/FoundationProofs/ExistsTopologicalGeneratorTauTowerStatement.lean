import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTopologicalGeneratorTauTower
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topological_generator_tau_tower : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ T : Tower p Ω, ∃ τ ∈ Ggeo p Ω, ∀ n, τ (T.qq n) = T.ζ n * T.qq n := by
  first | exact @GlobalTheory.K5.TauGen.main | exact GlobalTheory.K5.TauGen.main | (intros; apply GlobalTheory.K5.TauGen.main <;> assumption)
