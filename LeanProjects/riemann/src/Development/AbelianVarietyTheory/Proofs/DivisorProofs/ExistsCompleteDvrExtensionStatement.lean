import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrExtension
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_dvr_extension : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V], ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : V →+* O), Function.Injective φ ∧ IsLocalHom φ := by
  first | exact @GlobalTheory.CompleteDVR.exists_complete | exact GlobalTheory.CompleteDVR.exists_complete | (intros; apply GlobalTheory.CompleteDVR.exists_complete <;> assumption)
