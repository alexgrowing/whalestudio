import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellCharacterDistinct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_character_distinct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ), (∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1) → (∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) → a' < a →
    ∀ b b' : SizeMatrix (Two (Fin a) (Fin a')) (fun j : Fin 3 => Fin (blk3 m j)), b ≠ b' →
      ∃ t₁ t₂ : kˣ, cellChar k a a' α₀ β₀ b.1 t₁ t₂ ≠ cellChar k a a' α₀ β₀ b'.1 t₁ t₂ := by
  first | exact @GlobalTheory.IndLineGL.CellCharNe.cellChar_ne_of_ne | exact GlobalTheory.IndLineGL.CellCharNe.cellChar_ne_of_ne | (intros; apply GlobalTheory.IndLineGL.CellCharNe.cellChar_ne_of_ne <;> assumption)
