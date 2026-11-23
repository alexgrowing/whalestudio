import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirDifferenceOperatorEquivariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimirDifferenceOperator_equivariant : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ g ∈ UJset ε, ∀ v, Sm ε σ v → casOp σ (kB ε) (pB ε) (σ g v) = σ g (casOp σ (kB ε) (pB ε) v) := by
  first | exact @GlobalTheory.TypeSum.CasEquiv.casOp_equivariant | exact GlobalTheory.TypeSum.CasEquiv.casOp_equivariant | (intros; apply GlobalTheory.TypeSum.CasEquiv.casOp_equivariant <;> assumption)
