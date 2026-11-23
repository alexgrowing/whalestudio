import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpi
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operator_sequence_sum_epi : ∀ {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}, OpSeq k M T d → ∀ e, Epi (KerSeq.sumMap T d e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq | exact GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq | (intros; apply GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq <;> assumption)
