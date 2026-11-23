import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveAdicCompletionMapOfFinite
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_adicCompletion_map_of_finite : ∀ (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N] [Module.Finite D N], Function.Injective (algebraMap D N) → ∀ J : Ideal D, ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N, Function.Injective f := by
  first | exact @GlobalTheory.adicCompletion_injective_ringHom_of_finite | exact GlobalTheory.adicCompletion_injective_ringHom_of_finite | (intros; apply GlobalTheory.adicCompletion_injective_ringHom_of_finite <;> assumption)
