import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentTwistCharacterContinuous
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_twist_character_continuous : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] (H : Set G) (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (χ : G → ℂ), 0 < d → (∀ s, IsNilpotent (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ))) → (∀ γ ∈ H, ρ γ = 1) → (∀ i j, Continuous fun s => ρ s i j) → ∃ lam : G →* ℂˣ, (∀ s, ((lam s : ℂˣ) : ℂ) = χ s) ∧ Continuous (fun s => ((lam s : ℂˣ) : ℂ)) ∧ ∀ γ ∈ H, lam γ = 1 := by
  first | exact @GlobalTheory.scalar_part_character | exact GlobalTheory.scalar_part_character | (intros; apply GlobalTheory.scalar_part_character <;> assumption)
