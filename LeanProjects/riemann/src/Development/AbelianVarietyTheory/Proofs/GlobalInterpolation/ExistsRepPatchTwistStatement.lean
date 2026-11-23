import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepPatchTwist
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_agreeing_on_kernels : ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (ρ₀ ρ' : Γ →* GL (Fin n) k) (η₀ η : Γ →* ℤˣ) (P : GL (Fin n) k) (s : Γ), η₀ s = 1 → η s = -1 → (∀ g, η₀ g = 1 → η g = 1 → ρ' g = P⁻¹ * ρ₀ g * P) → (∀ Y : Matrix (Fin n) (Fin n) k, (∀ g, η₀ g = 1 → η g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ((ρ₀ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ∃ ρ : Γ →* GL (Fin n) k, (∀ g, η₀ g = 1 → ρ g = ρ₀ g) ∧ ∀ g, η g = 1 → ρ g = P * ρ' g * P⁻¹ := by
  first | exact @GlobalTheory.exists_rep_patch_twist | exact GlobalTheory.exists_rep_patch_twist | (intros; apply GlobalTheory.exists_rep_patch_twist <;> assumption)
