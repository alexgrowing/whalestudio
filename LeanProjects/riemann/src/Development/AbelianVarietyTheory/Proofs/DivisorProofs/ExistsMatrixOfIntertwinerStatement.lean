import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixOfIntertwiner
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_of_intertwiner : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)), IsFrame ρ e → IsFrame ρ' e' → (∀ l, X * ρ l = ρ' l * X) → ∃ Y, IsMat e e' X Y := by
  first | exact @GlobalTheory.DetInv.exists_isMat_of_equivariant | exact GlobalTheory.DetInv.exists_isMat_of_equivariant | (intros; apply GlobalTheory.DetInv.exists_isMat_of_equivariant <;> assumption)
