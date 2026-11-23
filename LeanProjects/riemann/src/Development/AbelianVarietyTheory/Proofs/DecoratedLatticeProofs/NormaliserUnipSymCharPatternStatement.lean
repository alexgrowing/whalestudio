import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormaliserUnipSymCharPattern
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normaliser_unipSym_char_pattern : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → 2 ≤ κ → ∀ ψ : AddChar k ℂ, ψ ≠ 1 → ∀ a : Fin n → Fin n → k, (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ M : GL (Fin n) k, (∀ h ∈ unipSym k n ρ κ, M * h * M⁻¹ ∈ unipSym k n ρ κ ∧ ψ (edgeVal ρ κ a (M * h * M⁻¹)) = ψ (edgeVal ρ κ a h)) → (∀ h ∈ unipSym k n ρ κ, M⁻¹ * h * M ∈ unipSym k n ρ κ) → ∃ s c : kˣ, ∃ h ∈ unipSym k n ρ κ, (M : Matrix (Fin n) (Fin n) k) = midDiag n ρ κ (s : k) (c : k) * (h : Matrix (Fin n) (Fin n) k) := by
  first | exact @GlobalTheory.SymNorm.normaliser_unipSym_char | exact GlobalTheory.SymNorm.normaliser_unipSym_char | (intros; apply GlobalTheory.SymNorm.normaliser_unipSym_char <;> assumption)
