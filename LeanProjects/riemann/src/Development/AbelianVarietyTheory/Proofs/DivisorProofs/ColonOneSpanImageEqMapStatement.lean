import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonOneSpanImageEqMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colon_one_span_image_eq_map_colon : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
    ∀ (A : Submodule (𝓞 E) E), A.FG → (1 : E) ∈ A →
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := by
  first | exact @GlobalTheory.colon_one_span_image_eq_map | exact GlobalTheory.colon_one_span_image_eq_map | (intros; apply GlobalTheory.colon_one_span_image_eq_map <;> assumption)
