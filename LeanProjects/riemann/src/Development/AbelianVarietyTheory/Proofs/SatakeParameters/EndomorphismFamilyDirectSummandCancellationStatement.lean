import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismFamilyDirectSummandCancellation
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphismFamily_direct_summand_cancellation : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V'] [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V) (b : ι → Module.End k V') (c : ι → Module.End k U), (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) → ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by
  first | exact @GlobalTheory.endFamily_cancel | exact GlobalTheory.endFamily_cancel | (intros; apply GlobalTheory.endFamily_cancel <;> assumption)
