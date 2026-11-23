import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdArgRealUnitEqOne
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_arg_real_unit_eq_one' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime → 2 < q →
    ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    (∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E)) →
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.prod_arg_real_unit_eq_one | exact GlobalTheory.prod_arg_real_unit_eq_one | (intros; apply GlobalTheory.prod_arg_real_unit_eq_one <;> assumption)
