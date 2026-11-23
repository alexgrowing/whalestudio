import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvReductionMulFlagTranslationMemRowLevelGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd

theorem reindex_symm_reindex {κ : Type} [CommRing κ] {a b : ℕ} (e : Fin a ≃ Fin b) (y : GL (Fin a) κ) :
    Units.map (Matrix.reindexAlgEquiv κ κ e.symm).toMonoidHom (Units.map (Matrix.reindexAlgEquiv κ κ e).toMonoidHom y) = y := by
  apply Units.ext
  ext i j
  simp [Matrix.reindexAlgEquiv_apply]

theorem of_reindex_mem_HK {κ : Type} [CommRing κ] {a n r t m : ℕ} (h : a = n) (hn : n = r + m * t) (hra : r ≤ a)
    (y : GL (Fin a) κ)
    (hy : Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y ∈ Formalism.L2.Col.HK n κ r (List.replicate m t)) :
    y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ Formalism.L2.DIV.upperLeftBlock hra y = 1 := by
  subst h
  rw [reindex_finCongr_rfl] at hy
  obtain ⟨hUT, h1⟩ := Formalism.L2.Col.mem_HK.1 hy
  have hb : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := by
    intro i j hij
    refine hUT (show Formalism.L2.Col.coarse r (List.replicate m t) j.val < Formalism.L2.Col.coarse r (List.replicate m t) i.val from ?_)
    rw [coarse_eq_blkOf hn, coarse_eq_blkOf hn]
    exact hij
  refine ⟨hb, ?_⟩
  apply Units.ext
  rw [Formalism.L2.DIV.upper_block_val_submatrix hra (Formalism.L2.DIV.blockTri_blkOf_le r t hb), Units.val_one]
  ext i j
  rw [Matrix.submatrix_apply, h1 _ _ i.2 j.2]
  simp [Matrix.one_apply, Fin.ext_iff]

theorem of_reindex_mem_HQ {κ : Type} [CommRing κ] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y ∈ Formalism.L2.Col.blockUT n κ r [b]) :
    y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  subst h
  rw [reindex_finCongr_rfl] at hy
  intro i j hij
  refine hy (show Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val from ?_)
  rw [coarseBlockIndex_eq_twoBlock hn, coarseBlockIndex_eq_twoBlock hn]
  exact hij

theorem redG_ptE_of (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) {U : Set I.ι}
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X')
    (hSt : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈ Formalism.L2.DIV.St L.βX)
    (hz : ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
    (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :
    Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ w =
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) :=
  redAt_reindex (finCongr (rank_X' X)) L.βX hL.beta.2 _ hSt (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz) w.1

set_option maxHeartbeats 1000000 in

theorem mem_J_of_redG_mem_grp : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') (hz : RowAd.ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp →
      h ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J := by
  intro X px I U L hI hL t h hz hred
  have hβ : L.βX = 1 := hL.beta.2
  have hSt : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈ Formalism.L2.DIV.St L.βX := by
    have h1 := reindex_mem_St_one (finCongr (rank_X' X)).symm (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz)
    have e2 : Units.map (Matrix.reindexAlgEquiv (Formalism.IndefR.Lev.EAf X.toD7) (Formalism.IndefR.Lev.EAf X.toD7)
        (finCongr (rank_X' X)).symm).toMonoidHom (ptE X h) = Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) :=
      reindex_symm_reindex _ _
    rw [hβ]
    exact e2 ▸ h1
  have hUA : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈
      Formalism.L2.DIV.UA X.toD7.sp.cm X.toD7.sp.X'.gram := by
    obtain ⟨g, hg⟩ := h.2
    rw [← hg]
    exact GlobalTheory.LevSplit.finE_mem_UA X.toD7.sp.X' g
  have hw : ∀ w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1,
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∈
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1 w).H := fun w => by
    rw [← redG_ptE_of X I L hL t h hSt hz w]
    exact hred w (Set.mem_univ _)
  have hG : ∀ PP ∈ (L.datXt t).Pg,
      Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _)) ∈
                Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (L.datXt t).r (L.datXt t).t) ∧
        Formalism.L2.DIV.upperLeftBlock (L.datXt t).hr
          (Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) = 1 := by
    intro PP hPP
    have hP : PP ∈ (X.B.primes px).vGs := by
      have hP' : PP ∈ L.Pg := hPP
      rw [hL.Pg] at hP'
      exact hP'
    have hm := hw ⟨PP, by classical exact Finset.mem_union_left _ hP⟩
    rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ hP] at hm
    exact of_reindex_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr _ hm
  have hQ : ∀ PP ∈ (L.datXt t).Q,
      Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (L.datXt t).r) := by
    intro PP hPP
    have hq : PP ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      have hP' : PP ∈ L.Q t := hPP
      have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
        simp only [ColIn.Q, tup_ixOf]
      rw [hL.Q t, e] at hP'
      exact hP'
    have hm := hw ⟨PP, by classical exact Finset.mem_union_right _ hq⟩
    by_cases hP : PP ∈ (X.B.primes px).vGs
    · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ hP] at hm
      exact Formalism.L2.DIV.blockTri_blkOf_le _ _
        (of_reindex_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr _ hm).1
    · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ _ hP] at hm
      exact of_reindex_mem_HQ (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) _ hm
  exact ⟨Formalism.L2.DIV.mem_parLev.2 ⟨hUA, hSt, fun PP hP => (hG PP hP).1, hQ⟩,
    Subgroup.mem_bot.2 (funext fun PP => (hG PP.1 PP.2).2)⟩

end GlobalTheory.Mem.R3.RowDeco
