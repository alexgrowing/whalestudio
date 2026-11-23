import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBlockDetEqBlockDetOfSumPartitions
import Mathlib
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Divisibility.DefGroup
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dBlk_eq_blkDet_coarse : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (g : GL (Fin n) κ) (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]),
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  first | exact @GlobalTheory.secondBlockDet_eq_blockDet_of_sum_partitions | exact GlobalTheory.secondBlockDet_eq_blockDet_of_sum_partitions | (intros; apply GlobalTheory.secondBlockDet_eq_blockDet_of_sum_partitions <;> assumption)
