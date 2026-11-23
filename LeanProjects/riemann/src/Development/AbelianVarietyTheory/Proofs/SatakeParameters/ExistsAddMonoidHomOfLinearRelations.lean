import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsExtra

namespace GlobalTheory

theorem exists_addMonoidHom_of_linear_relations : ∀ (M ι T : Type) [AddCommGroup T] [Module ℚ T] (Y : ι → M → ℚ) (t : ι → T), (∀ (s : Finset ι) (c : ι → ℚ), ∑ i ∈ s, c i • Y i = 0 → ∑ i ∈ s, c i • t i = 0) → ∃ Ξ : (M → ℚ) →+ T, ∀ i, Ξ (Y i) = t i := by
  first
  | exact @_root_.GlobalTheory.NormBoundTheorem.main
  | exact _root_.GlobalTheory.NormBoundTheorem.main
  | (apply _root_.GlobalTheory.NormBoundTheorem.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundTheorem.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundTheorem.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundTheorem.main ..)

end GlobalTheory
