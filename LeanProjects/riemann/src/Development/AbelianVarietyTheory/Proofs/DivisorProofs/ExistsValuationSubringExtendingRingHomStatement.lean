import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringExtendingRingHom
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_extending_ringHom : ∀ (W Ω k : Type) [CommRing W] [Field Ω] [Field k] [IsAlgClosed k] (j : W →+* Ω), Function.Injective j → ∀ g : W →+* k, ∃ (U : ValuationSubring Ω) (hU : ∀ w, j w ∈ U) (h : U →+* k), ∀ w, h ⟨j w, hU w⟩ = g w := by
  first | exact @GlobalTheory.ValExt.exists_valuationSubring_ext | exact GlobalTheory.ValExt.exists_valuationSubring_ext | (intros; apply GlobalTheory.ValExt.exists_valuationSubring_ext <;> assumption)
