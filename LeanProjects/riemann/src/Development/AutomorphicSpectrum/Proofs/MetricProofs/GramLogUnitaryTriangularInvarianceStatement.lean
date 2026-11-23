import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramLogUnitaryTriangularInvariance
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_flag_domain_nondegenerate_minors : ∀ (N j : ℕ), j ≤ N → IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∧ ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∀ k, (gramHead (sigForm N j) k g).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors | exact GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flagDomain_open_and_minors <;> assumption)
