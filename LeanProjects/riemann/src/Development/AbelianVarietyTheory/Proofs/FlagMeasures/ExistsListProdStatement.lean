import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsListProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irr_pairs_char_prod_eq_sum : ∀ (G₁ G₂ : Type) [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ), IsChar Φ → ∃ L : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧ ∀ x y, Φ (x, y) = (L.map fun p => p.1 x * p.2 y).sum := by
  first | exact @GlobalTheory.GLm.ProdChar.exists_list_prod | exact GlobalTheory.GLm.ProdChar.exists_list_prod | (intros; apply GlobalTheory.GLm.ProdChar.exists_list_prod <;> assumption)
