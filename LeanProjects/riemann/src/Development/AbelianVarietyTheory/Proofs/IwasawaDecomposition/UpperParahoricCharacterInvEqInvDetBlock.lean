import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.LamQInv

theorem coarseBlockIndex_single_eq_twoBlock {a r b : ℕ} (hn : a = r + b) (i : Fin a) :
    Formalism.L2.Col.coarse r [b] i.val = Formalism.L2.DIV.blk2 r i := by
  unfold Formalism.L2.DIV.blk2
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have : i.val - r < b := by omega
    simp [Formalism.L2.Col.blkIdx, this]

theorem lamQ_castGL_inv : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * 1 ∈ Formalism.L2.Col.HQ κ n r b),
    Formalism.L2.Col.lamQ χ n r b ⟨_, hz⟩ = (χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 y))⁻¹ := by
  intro κ K _ _ a n r b h hn y hy χ hz
  subst h
  have hc : LiftBrg.castGL (rfl : a = a) y = y := by
    ext; simp [LiftBrg.castGL]
  have hy' : y ∈ Formalism.L2.Col.blockUT a κ r [b] := by
    intro i j hij
    apply hy
    show Formalism.L2.DIV.blk2 r j < Formalism.L2.DIV.blk2 r i
    rw [← coarseBlockIndex_single_eq_twoBlock hn, ← coarseBlockIndex_single_eq_twoBlock hn]
    exact hij
  have he : (⟨_, hz⟩ : ↥(Formalism.L2.Col.HQ κ a r b)) = (⟨y, hy'⟩ : ↥(Formalism.L2.Col.HQ κ a r b))⁻¹ := by
    ext1
    simp [hc]
  rw [he, map_inv, Formalism.L2.Col.lamQ_apply]
  congr 2
  ext
  rw [Formalism.L2.Col.blkDet_val, Formalism.L2.DIV.diag_block_det_val 1 hy]
  rw [Matrix.toSquareBlock_def]
  let e : {i : Fin a // Formalism.L2.Col.coarse r [b] i.val = 1} ≃ {i : Fin a // Formalism.L2.DIV.blk2 r i = 1} :=
    Equiv.subtypeEquivRight (fun i => by rw [coarseBlockIndex_single_eq_twoBlock hn])
  exact Matrix.det_submatrix_equiv_self e (((y : GL (Fin a) κ) : Matrix (Fin a) (Fin a) κ).submatrix (Subtype.val : {i : Fin a // Formalism.L2.DIV.blk2 r i = 1} → Fin a) Subtype.val)

end GlobalTheory.Mem.R3.LiftBrg.LamQInv
