import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfNormOneValuationSubOneSmall
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_norm_one_valuation_sub_one_small : ∀ (E : Type) [Field E] [NumberField E] (ε : E) (w : HeightOneSpectrum (𝓞 E)) (K : ℕ), Module.finrank ℚ E < K → (∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ε ≤ 1) → (∀ φ : E →+* ℂ, ‖φ ε‖ = 1) → w.valuation E (ε - 1) ≤ WithZero.exp (-(K : ℤ)) → ε = 1 := by
  first | exact @GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le | exact GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le | (intros; apply GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le <;> assumption)
