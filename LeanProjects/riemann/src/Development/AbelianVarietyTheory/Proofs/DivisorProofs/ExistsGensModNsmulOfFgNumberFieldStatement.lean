import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensModNsmulOfFgNumberField
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gens_mod_nsmul_of_fg_numberField : ∀ (E : Type) [Field E] [NumberField E] (r M : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → Λ.FG → ∃ e : Fin r → Fin r → E, (∀ i, e i ∈ Λ) ∧ ∀ x ∈ Λ, ∃ o : Fin r → 𝓞 E, ∃ y ∈ Λ, x = ∑ i, o i • e i + M • y := by
  first | exact @GlobalTheory.GensModNsmul.exists_gens_mod_nsmul | exact GlobalTheory.GensModNsmul.exists_gens_mod_nsmul | (intros; apply GlobalTheory.GensModNsmul.exists_gens_mod_nsmul <;> assumption)
