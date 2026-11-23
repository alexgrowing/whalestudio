import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceExistsUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFormTrace_exists_unique : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], IsTrDR k K L (trDR k K L) ∧ ∀ T, IsTrDR k K L T → T = trDR k K L := by
  first | (exact @GlobalTheory.W1.trDR_isTrDR_unique) | (exact GlobalTheory.W1.trDR_isTrDR_unique) | (intros; apply GlobalTheory.W1.trDR_isTrDR_unique <;> assumption)
