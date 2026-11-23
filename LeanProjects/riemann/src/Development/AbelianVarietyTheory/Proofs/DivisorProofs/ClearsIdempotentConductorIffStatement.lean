import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearsIdempotentConductorIff
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clears_idempotent_conductor_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (l : ℕ), l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D := by
  first | exact @GlobalTheory.CondAway.clearsIdem_condQ_iff | exact GlobalTheory.CondAway.clearsIdem_condQ_iff | (intros; apply GlobalTheory.CondAway.clearsIdem_condQ_iff <;> assumption)
