import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowValuationDivSubOneLeOfCongr
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_valuation_div_sub_one_le_of_congr : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), c ≠ 0 → ∀ n : ℕ, ∃ N : ℕ, ∀ k : 𝓞 E, k - c ∈ v.asIdeal ^ N → v.valuation E ((k : E) / (c : E) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.exists_pow_valuation_div_sub_one_le | exact GlobalTheory.exists_pow_valuation_div_sub_one_le | (intros; apply GlobalTheory.exists_pow_valuation_div_sub_one_le <;> assumption)
