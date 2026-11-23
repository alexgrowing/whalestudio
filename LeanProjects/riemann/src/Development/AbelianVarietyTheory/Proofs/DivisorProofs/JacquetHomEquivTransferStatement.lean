import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetHomEquivTransfer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hom_equiv_transfer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) (P Q P₁ : Type) [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P₁] [Module ℂ P₁] (π : Representation ℂ (GL (Fin n) k) P)
    (π' : Representation ℂ (GL (Fin n) k) Q) (σ₁ : Representation ℂ (GL (Fin m) k) P₁) (ξ₁ ξ₂ : kˣ →* ℂˣ),
    Nonempty (π.Equiv π') →
    HomLeOne (jac e π') (twist (leviTgt σ₁ ξ₁ ξ₂) (deltaHalf k fun i : Fin 3 => Fin (blk3 m i))⁻¹) →
    HomLeOne (jacU e π) (leviTgt σ₁ ξ₁ ξ₂) := by
  first | exact @GlobalTheory.JacTransport.homLeOne_jacU_of_equiv | exact GlobalTheory.JacTransport.homLeOne_jacU_of_equiv | (intros; apply GlobalTheory.JacTransport.homLeOne_jacU_of_equiv <;> assumption)
