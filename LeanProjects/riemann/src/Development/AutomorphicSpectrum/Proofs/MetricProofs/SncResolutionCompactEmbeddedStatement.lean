import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCompactEmbedded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_resolution_compact_embedded : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → CompactSpace (SncRes.Pts P) ∧ ∀ p : (k : K) → ι k, IsOpen (SncRes.src P p) ∧ Topology.IsEmbedding (fun x : SncRes.src P p => SncRes.coord P p x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.compact_open_embedding | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.compact_open_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.compact_open_embedding <;> assumption)
