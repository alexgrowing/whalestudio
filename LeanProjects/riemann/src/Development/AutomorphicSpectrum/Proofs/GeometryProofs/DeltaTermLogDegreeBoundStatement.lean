import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaTermLogDegreeBound
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropFTop
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_term_log_degree_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ), j ≤ N → 2 ≤ p → ∃ e : ℝ, |e| ≤ N / ((p : ℝ) - 1) ∧ ((∀ n, ∃ σ, fr n = Sum.inl σ) → e = 0) ∧ ((∀ n, (∃ σ, fr n = Sum.inl σ) ↔ Odd n) → e = ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ ∀ Q : RP Ψ N, deltaTerm j p τ fr 1 Q = e * Real.log p * degFl Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one | exact GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one <;> assumption)
