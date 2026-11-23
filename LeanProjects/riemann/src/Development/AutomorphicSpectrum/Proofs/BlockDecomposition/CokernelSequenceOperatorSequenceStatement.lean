import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSequenceOperatorSequence
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerOpsComm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_sequence_operator_sequence : ∀ {X : AlgebraicGeometry.Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : GlobalTheory.CompanionTheory.GE.OpSeq (k + 1) M T d), GlobalTheory.CompanionTheory.GE.OpSeq k (GlobalTheory.CompanionTheory.GE.UV.cokSeq M T) (GlobalTheory.CompanionTheory.GE.UV.cokOps hM.comm) d := by
  first | exact @GlobalTheory.CompanionTheory.GE.UV.cokOpSeq | exact GlobalTheory.CompanionTheory.GE.UV.cokOpSeq | (intros; apply GlobalTheory.CompanionTheory.GE.UV.cokOpSeq <;> assumption)
