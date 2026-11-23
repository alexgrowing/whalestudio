import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairSplitSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclic_torsor_etale : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act → Algebra.Etale B D := by
  first | (exact @GlobalTheory.KeyOriginCut.etale_of_isZTorsor) | (exact GlobalTheory.KeyOriginCut.etale_of_isZTorsor) | (intros; apply GlobalTheory.KeyOriginCut.etale_of_isZTorsor <;> assumption)
