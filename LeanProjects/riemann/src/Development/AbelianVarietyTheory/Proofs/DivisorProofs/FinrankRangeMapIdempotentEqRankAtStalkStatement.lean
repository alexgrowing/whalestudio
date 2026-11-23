import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMapIdempotentEqRankAtStalk
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_map_idempotent_eq_rankAtStalk : ∀ (A : Type) [CommRing A] (n : ℕ) (P : Matrix (Fin n) (Fin n) A), P * P = P →
    ∀ (k : Type) [Field k] (g : A →+* k),
      Module.finrank k (LinearMap.range (P.map g).mulVecLin) =
        Module.rankAtStalk (LinearMap.range P.mulVecLin) (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
  first | (exact @GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk) | (exact GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk) | (intros; apply GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk  <;> assumption)
