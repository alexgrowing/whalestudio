import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceProjectionFormula
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFormTrace_projection_formula : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], ∀ (α : DR k K) (β : DR k L), trDR k K L (mapDR k K L α * β) = α * trDR k K L β ∧ trDR k K L (β * mapDR k K L α) = trDR k K L β * α := by
  first | (exact @GlobalTheory.W1.trDR_projection) | (exact GlobalTheory.W1.trDR_projection) | (intros; apply GlobalTheory.W1.trDR_projection <;> assumption)
