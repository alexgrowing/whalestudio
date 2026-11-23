import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_primesOver_eq_finrank_of_unramified_split : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) → (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  first | exact @GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq | exact GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq | (intros; apply GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq <;> assumption)
