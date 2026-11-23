import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKilledByLowerNilradicalActBlockDiagonal
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKilledByLowerNilradical_act_blockDiagonal : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ Z : Mat p q, IsKC Z → ∀ x : V, KilledByLower act x → KilledByLower act (act Z x) := by
  first | exact @GlobalTheory.KilledByLowerStable.killedByLower_act | exact GlobalTheory.KilledByLowerStable.killedByLower_act | (intros; apply GlobalTheory.KilledByLowerStable.killedByLower_act <;> assumption)
