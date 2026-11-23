import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIdeleEqIdl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplMapSplitProj

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit
open GlobalTheory.LineFrame

namespace GlobalTheory.LineFrame

theorem unipRad_frame_blocks : ∀ (k : Type) [Field k] (N m : ℕ) (hr : N = m + 2) (h2 : 2 ≤ N) (n : GL (Fin N) k),
    n ∈ unipRad k (linePlace h2) →
      ∃ (X : Matrix (Fin 1) (Fin m ⊕ Fin 1) k) (Y : Matrix (Fin m) (Fin 1) k),
        (n : Matrix (Fin N) (Fin N) k).submatrix (GlobalTheory.LineFrame.frameEquiv hr) (GlobalTheory.LineFrame.frameEquiv hr) =
          Matrix.fromBlocks 1 X 0 (Matrix.fromBlocks 1 Y 0 1) := by
  intro k _ N m hr h2 n hn
  have hu := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.1 hn
  let g : Fin 1 ⊕ Fin m ⊕ Fin 1 → Fin 3 := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
  have hb : ∀ x, blk (linePlace h2) (frameEquiv hr x) = g x := by
    rintro (i | j | i)
    · have e : frameEquiv hr (.inl i) = linePlace h2 ⟨0, ⟨0, by simp [tripSizes]⟩⟩ := by
        apply Fin.ext
        rw [frameEquiv_inl, GlobalTheory.BlockForms.LeviLoc.tripPlace_val]
        simp
      rw [e, blk_apply]
      rfl
    · have e : frameEquiv hr (.inr (.inl j)) = linePlace h2 ⟨1, ⟨j.val, by simp [tripSizes]; omega⟩⟩ := by
        apply Fin.ext
        rw [frameEquiv_mid, GlobalTheory.BlockForms.LeviLoc.tripPlace_val]
        simp; omega
      rw [e, blk_apply]
      rfl
    · have e : frameEquiv hr (.inr (.inr i)) = linePlace h2 ⟨2, ⟨0, by simp [tripSizes]; omega⟩⟩ := by
        apply Fin.ext
        rw [frameEquiv_inr, GlobalTheory.BlockForms.LeviLoc.tripPlace_val]
        simp; omega
      rw [e, blk_apply]
      rfl
  have hu' : ∀ x y, ¬ g x < g y →
      (n : Matrix (Fin N) (Fin N) k) (frameEquiv hr x) (frameEquiv hr y) = (1 : Matrix (Fin 1 ⊕ Fin m ⊕ Fin 1) _ k) x y := by
    intro x y hxy
    rw [hu _ _ (by rw [hb, hb]; exact hxy)]
    simp only [Matrix.one_apply, (frameEquiv hr).injective.eq_iff]
  refine ⟨fun i c => (n : Matrix (Fin N) (Fin N) k) (frameEquiv hr (.inl i)) (frameEquiv hr (.inr c)),
    fun j i => (n : Matrix (Fin N) (Fin N) k) (frameEquiv hr (.inr (.inl j))) (frameEquiv hr (.inr (.inr i))), ?_⟩
  ext (i | i | i) (j | j | j) <;> simp only [Matrix.submatrix_apply] <;>
    first
    | rfl
    | (rw [hu' _ _ (by simp [g])]; simp [Matrix.one_apply, Matrix.fromBlocks])

end GlobalTheory.LineFrame
