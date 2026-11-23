import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValVpNatCastPow
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_pow_eq_alt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], ∀ (l : ℕ), l ≠ 0 → (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ k : ℕ, val_vp O l (algebraMap O K ((l : O) ^ k)) = ((k : ℚ) : WithTop ℚ) := by
  first | exact @GlobalTheory.val_vp_natCast_pow | exact GlobalTheory.val_vp_natCast_pow | (intros; apply GlobalTheory.val_vp_natCast_pow <;> assumption)
