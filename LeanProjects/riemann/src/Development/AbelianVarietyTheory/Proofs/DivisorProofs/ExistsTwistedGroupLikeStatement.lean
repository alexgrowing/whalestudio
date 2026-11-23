import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedGroupLike
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_groupLike' : ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H] [Bialgebra K H] [Coalgebra.IsCocomm K H] [Module.Finite K H] (c : H ⊗[K] H), IsUnit c → c ⊗ₜ[K] (1 : H) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) c = (Algebra.TensorProduct.assoc K K K H H H).symm ((1 : H) ⊗ₜ[K] c * Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) c) → Algebra.TensorProduct.comm K H H c = c → ∃ u : H, u ≠ 0 ∧ c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u := by
  first | exact @GlobalTheory.exists_twisted_groupLike | exact GlobalTheory.exists_twisted_groupLike | (intros; apply GlobalTheory.exists_twisted_groupLike <;> assumption)
