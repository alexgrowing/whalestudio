import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsNoetherianRingOfDirectedPureUnion
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNoetherianRing_of_directed_pure_union' : ∀ (S : Type) [CommRing S] [IsLocalRing S] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S), Monotone R → (∀ x : S, ∃ i, x ∈ R i) → (∀ i, IsNoetherianRing (R i)) → (∀ i, ((maximalIdeal S).comap (R i).subtype).map (R i).subtype = maximalIdeal S) → (∀ i (J : Ideal (R i)), (J.map (R i).subtype).comap (R i).subtype = J) → IsNoetherianRing S := by
  first | (exact @GlobalTheory.isNoetherianRing_of_directed_pure_union) | (exact GlobalTheory.isNoetherianRing_of_directed_pure_union) | (intros; apply GlobalTheory.isNoetherianRing_of_directed_pure_union  <;> assumption)
