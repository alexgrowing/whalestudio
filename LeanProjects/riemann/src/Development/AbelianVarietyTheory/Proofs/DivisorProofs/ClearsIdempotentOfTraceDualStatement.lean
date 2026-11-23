import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearsIdempotentOfTraceDual
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clears_idempotent_of_trace_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], Nat.card (E →+* K) = Module.finrank ℚ E → ∀ D : O, (∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y) → ClearsIdem K (⊤ : Ideal (OF E)) D := by
  first | exact @GlobalTheory.DualCrit.clearsIdem_top_of_dual | exact GlobalTheory.DualCrit.clearsIdem_top_of_dual | (intros; apply GlobalTheory.DualCrit.clearsIdem_top_of_dual <;> assumption)
