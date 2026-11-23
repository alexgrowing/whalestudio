import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerJInvariantTranscendental
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerJInvariant_transcendental : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε), Transcendental Ω X.jK := by
  first | exact @GlobalTheory.KZ.Tower.jK_transcendental | exact GlobalTheory.KZ.Tower.jK_transcendental | (intros; apply GlobalTheory.KZ.Tower.jK_transcendental <;> assumption)
