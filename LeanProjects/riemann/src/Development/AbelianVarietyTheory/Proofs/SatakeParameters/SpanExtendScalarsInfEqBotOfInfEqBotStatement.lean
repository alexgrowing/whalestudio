import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanExtendScalarsInfEqBotOfInfEqBot
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_extendScalars_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ → Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  first | exact @GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot | exact GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot | (intros; apply GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot <;> assumption)
