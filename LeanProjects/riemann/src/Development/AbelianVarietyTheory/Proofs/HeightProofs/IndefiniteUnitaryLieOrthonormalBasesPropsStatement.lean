import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IndefiniteUnitaryLieOrthonormalBasesProps
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_unitary_lie_orthonormal_bases_props : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε ∧ (kB ε i)ᴴ = -kB ε i ∧ hs (kB ε i) ≤ 1) ∧ ∀ b, pB ε b ∈ lieSet ε ∧ (pB ε b)ᴴ = pB ε b := by
  first | exact @GlobalTheory.TypeSum.CasBasis.bases_mem_lie | exact GlobalTheory.TypeSum.CasBasis.bases_mem_lie | (intros; apply GlobalTheory.TypeSum.CasBasis.bases_mem_lie <;> assumption)
