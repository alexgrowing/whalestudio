import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubring
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring : ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (c M : ℕ) (ζ : K) (a b : ℤ), 0 < M → Nat.Coprime c M → ¬ (M : ℤ) ∣ a → ζ ^ b ∈ R → ζ ^ (-b) ∈ R → ∀ n : ℕ, GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M ζ a b n ∈ R := by
  first | exact @GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring | exact GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring | (intros; apply GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring; all_goals assumption)
