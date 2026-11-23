import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotientSubfieldEqMulRankOrder
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_quotientSubfield_eq_mul_rank_order : ∀ (k K : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [Field K] [CharZero K] (ι : k →+* K) (D : ℕ) (x : Fin (D + 1) → K), Function.Injective ι → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → Module.finrank (ratF x) K = Module.finrank (Subfield.closure (Set.range ι ∪ Set.range fun j : Fin D => x j.succ / x 0)) K * Module.finrank ℤ k ∧ Function.Injective (MvPolynomial.eval₂Hom ι fun j : Fin D => x j.succ / x 0) := by
  first | exact @GlobalTheory.HSAmp.finrank_ratF_eq_mul_rank | exact GlobalTheory.HSAmp.finrank_ratF_eq_mul_rank | (intros; apply GlobalTheory.HSAmp.finrank_ratF_eq_mul_rank <;> assumption)
