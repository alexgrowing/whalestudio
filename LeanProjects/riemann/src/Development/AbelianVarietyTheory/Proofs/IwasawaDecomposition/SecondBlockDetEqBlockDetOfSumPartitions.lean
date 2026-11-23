import Mathlib
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Divisibility.DefGroup
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem blkOf_eq_coarse {n r t : ℕ} (hn : n = r + t) :
    (Formalism.L2.DIV.blkOf r t : Fin n → ℕ) = fun a => Formalism.L2.Col.coarse r [t] a.val := by
  funext a
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]; simp [Formalism.L2.DIV.blkOf, h]
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    have h2 : a.val - r < t := by omega
    simp [Formalism.L2.DIV.blkOf, h, Formalism.L2.Col.blkIdx, h2, Nat.div_eq_of_lt h2]

theorem twoBlocks_eq_coarse_of_add {n r t : ℕ} (hn : n = r + t) :
    (Formalism.L2.DIV.blk2 r : Fin n → ℕ) = fun a => Formalism.L2.Col.coarse r [t] a.val := by
  funext a
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]; simp [Formalism.L2.DIV.blk2, h]
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp h)]
    have h2 : a.val - r < t := by omega
    simp [Formalism.L2.DIV.blk2, h, Formalism.L2.Col.blkIdx, h2]

theorem lowerBlockDet_coarse_partition_eq_blockDet_upperTri {κ : Type} [CommRing κ] {n r t : ℕ} (g : GL (Fin n) κ)
    (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]) :
    Formalism.L2.DIV.dBlk (fun a : Fin n => Formalism.L2.Col.coarse r [t] a.val) 1 g =
      Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  have hg' : g ∈ Formalism.L2.DIV.blockTri (fun a : Fin n => Formalism.L2.Col.coarse r [t] a.val) := hg
  apply Units.ext
  rw [Formalism.L2.DIV.diag_block_det_val 1 hg', Formalism.L2.Col.blkDet_val]
  rfl

theorem secondBlockDet_eq_blockDet_of_sum_partitions : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (g : GL (Fin n) κ) (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]),
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  intro κ _ n r t hn g hg
  refine ⟨?_, ?_⟩
  · rw [blkOf_eq_coarse hn]; exact lowerBlockDet_coarse_partition_eq_blockDet_upperTri g hg
  · rw [twoBlocks_eq_coarse_of_add hn]; exact lowerBlockDet_coarse_partition_eq_blockDet_upperTri g hg

end GlobalTheory
