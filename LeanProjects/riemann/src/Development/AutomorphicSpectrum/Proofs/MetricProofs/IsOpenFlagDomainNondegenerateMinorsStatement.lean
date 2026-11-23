import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsOpenFlagDomainNondegenerateMinors
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_domain_unitary_triangular : ∀ (N j : ℕ), j ≤ N → ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∃ u b : Matrix (Fin N) (Fin N) ℂ, gramOf (sigForm N j) u = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ)) ∧ b.BlockTriangular id ∧ IsUnit b.det ∧ u * g = b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.exists_unitary_translate_flag | exact GlobalTheory.CompanionTheory.Ar.PB.exists_unitary_translate_flag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.exists_unitary_translate_flag <;> assumption)
