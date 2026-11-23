import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellMiddleIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_middle_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.ThK.KP → ∀ (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ), IsSmoothChar α₀ → IsSmoothChar β₀ →
    (∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1) → (∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) →
    ∀ b : SizeMatrix (Two (Fin a) (Fin a')) (fun j : Fin 3 => Fin (blk3 m j)), b.1 false 0 = b.1 false 2 →
      (cellMid k α₀ β₀ b.1).IsIrreducible := by
  first | exact @GlobalTheory.IndLineGL.cellMid_isIrreducible_of_eq | exact GlobalTheory.IndLineGL.cellMid_isIrreducible_of_eq | (intros; apply GlobalTheory.IndLineGL.cellMid_isIrreducible_of_eq <;> assumption)
