import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory

theorem upqRep_vocabulary_agree : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : B.Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), (Formalism.MainNotions.S.IsDSHpk k r ε lam σ ↔ PI.UpqRep.IsDSHpk k r ε lam σ) ∧ (∀ v, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v ↔ PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) ∧ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ = PI.UpqRep.smoothVecs (k := k) (r := r) σ ∧ (Formalism.QuantumDeterminants.IsHCParam lam ↔ PI.UpqRep.IsHCParam lam) ∧ (∀ P, Formalism.MainNotions.S.IsCayleyU k r ε P ↔ PI.UpqRep.IsCayleyU k r ε P) ∧ Formalism.MainNotions.S.lowKSub ε lam σ = PI.UpqRep.lowKSub ε lam σ := by
  intro k r H _ _ _ σ ε lam
  exact ⟨Iff.rfl, fun _ => Iff.rfl, rfl, Iff.rfl, fun _ => Iff.rfl, rfl⟩

end GlobalTheory
