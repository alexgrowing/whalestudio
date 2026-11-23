import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockTriangularBlockIndexOfIffColBlockUTTwoBlock
import Mathlib
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Divisibility.DefGroup
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ g : GL (Fin n) κ,
    (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) ∧
      (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) := by
  first | exact @GlobalTheory.blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks | exact GlobalTheory.blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks | (intros; apply GlobalTheory.blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks <;> assumption)
