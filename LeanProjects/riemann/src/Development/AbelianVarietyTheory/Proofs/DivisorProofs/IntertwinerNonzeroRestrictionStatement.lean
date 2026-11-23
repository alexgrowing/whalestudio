import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerNonzeroRestriction
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_nonzero_restriction : ∀ {H V U Y : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H V) (σ : Representation ℂ H U)
    (θ : Representation ℂ H Y) {ι : Type} [Fintype ι] (E : ι → ρ.IntertwiningMap σ)
    (R S : Subrepresentation ρ) (φ : S.toRepresentation.IntertwiningMap θ) (s : S.toSubmodule),
    (s : V) ∈ R.toSubmodule → φ s ≠ 0 → (∀ v ∈ R.toSubmodule, (∀ i, E i v = 0) → v = 0) →
    ∃ (S' : Subrepresentation σ) (φ' : S'.toRepresentation.IntertwiningMap θ), φ' ≠ 0 := by
  first | exact @GlobalTheory.intertwining_peel | exact GlobalTheory.intertwining_peel | (intros; apply GlobalTheory.intertwining_peel <;> assumption)
