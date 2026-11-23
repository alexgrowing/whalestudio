import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionUniqueUpToIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
open IsLocalRing GlobalTheory.Pat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_unique_up_to_iso : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (φ' : R →+* S'), IsCplAt q φ → IsCplAt q φ' → ∃ e : S ≃+* S', (e : S →+* S').comp φ = φ' := by
  first | exact @GlobalTheory.Pat.isCplAt_unique | exact GlobalTheory.Pat.isCplAt_unique | (intros; apply GlobalTheory.Pat.isCplAt_unique <;> assumption)
