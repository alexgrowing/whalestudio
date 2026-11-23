import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetHomLeviTgtBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hom_leviTgt_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) (P P₁ : Type) [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (π : Representation ℂ (GL (Fin n) k) P)
    (σ₁ : Representation ℂ (GL (Fin m) k) P₁) (ξ₁ ξ₂ : kˣ →* ℂˣ),
    HomLeOne (jacU e π) (leviTgt σ₁ ξ₁ ξ₂) →
    ∀ A A' : P →ₗ[ℂ] (GL (Fin n) k → P₁), IsGLIndMap e π σ₁ ξ₁ ξ₂ A → IsGLIndMap e π σ₁ ξ₁ ξ₂ A' →
      A = 0 ∨ ∃ c : ℂ, A' = c • A := by
  first | exact @GlobalTheory.IndLineGL.glIndMap_proportional_of_jacquet | exact GlobalTheory.IndLineGL.glIndMap_proportional_of_jacquet | (intros; apply GlobalTheory.IndLineGL.glIndMap_proportional_of_jacquet <;> assumption)
