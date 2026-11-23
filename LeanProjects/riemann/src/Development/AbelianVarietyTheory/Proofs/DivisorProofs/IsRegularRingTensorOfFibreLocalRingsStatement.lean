import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingTensorOfFibreLocalRings
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularRing_tensor_of_regular_fibre_localizations : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q → IsRegularLocalRing (Localization.AtPrime n ⧸ (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) → IsRegularRing (T ⊗[S] K) := by
  first | exact @GlobalTheory.isRegularRing_tensor_of_fibre_localRings | exact GlobalTheory.isRegularRing_tensor_of_fibre_localRings | (intros; apply GlobalTheory.isRegularRing_tensor_of_fibre_localRings <;> assumption)
