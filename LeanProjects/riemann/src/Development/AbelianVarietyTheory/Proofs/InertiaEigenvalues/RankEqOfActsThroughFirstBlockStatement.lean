import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankEqOfActsThroughFirstBlock
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_eq_of_mulVec_through_first_block : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (F : Matrix (Fin n) (Fin n) K) (ε : Matrix (Fin r) (Fin r) K), (∀ u, e (F.mulVec u) = (ε.mulVec (e u).1, 0)) → F.rank = ε.rank := by
  first | exact @GlobalTheory.rank_eq_of_acts_through_first_block | exact GlobalTheory.rank_eq_of_acts_through_first_block | (intros; apply GlobalTheory.rank_eq_of_acts_through_first_block <;> assumption)
