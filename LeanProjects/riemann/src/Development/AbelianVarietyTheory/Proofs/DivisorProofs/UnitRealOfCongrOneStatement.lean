import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRealOfCongrOne
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_real_of_sub_one_mem_span_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime →
    ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E) := by
  first | exact @GlobalTheory.UnitReal.unit_real_of_congr_one | exact GlobalTheory.UnitReal.unit_real_of_congr_one | (intros; apply GlobalTheory.UnitReal.unit_real_of_congr_one <;> assumption)
