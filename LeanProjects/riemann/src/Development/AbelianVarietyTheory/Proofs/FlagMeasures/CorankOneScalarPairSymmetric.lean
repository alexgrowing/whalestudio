import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalSymm

open Formalism.L2.SG.NGCut

theorem scal_symm : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t := by
  intro D X Y u u' t t' hG hG' hs hsc
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t : TauC Y u u', t.G ≠ 0 → Gval (lf D (X.Fu u)) t.frame ≠ 0 := fun t h =>
    (Formalism.L2.SG.Pf.SatGram.gterm_G Y t) ▸ h
  have hlat : ∀ t : TauC Y u u', Submodule.IsLattice D.host.E t.lam := fun t =>
    ((Y.rowsOK u).1 t.lam t.mem).2.1.1
  have hLF : ∀ t : TauC Y u u', IsLift t.lam (lf D (X.Fu u)) := fun t =>
    ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : TauC Y u u', IsLift t.lam t.frame := fun t => t.rep.2.2.2.2.1
  obtain ⟨⟨hlam, hlam'⟩, -, hIS⟩ := (show Formalism.L2.SG.TermOp.scalT t t' from hsc)
  have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := hs
  unfold Formalism.L2.SG.TermOp.s0T at h1'
  rw [if_pos ⟨hlam, hlam'⟩] at h1'
  have hth := (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
    (hGv t hG)).1 h1'
  have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
  have hsym := CorankRelation.Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
    (hGv t hG) (hGv t' hG') (CorankRelation.frame_mem_iff t t') hth
  have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
  rw [hinv] at hsym
  have hs' : s0 t.lam (lf D (X.Fu u)) t'.frame t.frame (t.lin * t'.lin⁻¹) D.R.k = 1 :=
    (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' hG')).2 hsym
  have hback : ∀ y : (VS D).V, (t'.lin * t.lin⁻¹) ((t.lin * t'.lin⁻¹) y) = y := fun y => by
    show t'.lin (t.lin.symm (t.lin (t'.lin.symm y))) = y
    simp
  refine ⟨?_, ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    exact hs'
  · show Formalism.L2.SG.TermOp.scalT t' t
    refine ⟨⟨hlam.symm, hlam'.symm⟩, ?_, ?_⟩
    · rw [← hlam]; exact hs'
    · rw [← hlam]
      intro y2 hy2 y1 hy1 y2'' hy2'' y1' hy1' hd hd' al al'
      have hd1 : y1 - y2 ∈ Xsp (lf D (X.Fu u)) := by
        have := (Xsp (lf D (X.Fu u))).neg_mem hd
        simpa using this
      have hd2 : y2'' - (t'.lin * t.lin⁻¹) y1' ∈ Xsp t'.frame := by
        have h := (CorankRelation.frame_mem_iff t t' _).1 hd'
        rw [map_sub, hback] at h
        have := (Xsp t'.frame).neg_mem h
        simpa using this
      exact (hIS y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hd1 hd2 al al').symm

end GlobalTheory.ScalSymm
