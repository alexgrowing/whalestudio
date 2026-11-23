import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastPowMulValuationLeOneOfNotPowSuccDvdDiffer
import Mathlib
open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_prime_pow_mul_le_one_of_not_dvd_different : ∀ (l c : ℕ) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) → ∀ y : L, (∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1) → la.valuation L ((l : L) ^ c * y) ≤ 1 := by
  first | exact @GlobalTheory.natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal | exact GlobalTheory.natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal | (intros; apply GlobalTheory.natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal <;> assumption)
