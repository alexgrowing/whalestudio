import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameZEqLinZu

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem th21 (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0) (h2 : Gt t2 ≠ 0)
    (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) :
    t1.lam = t0.lam ∧ t2.lam = t0.lam ∧
    Th t0.lam (lf D (X.Fu u)) t2.frame t1.frame (t1.lin * t2.lin⁻¹) = Hp t0.lam (lf D (X.Fu u)) t2.frame := by
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  obtain ⟨hrow1, hs01⟩ := hR1
  obtain ⟨hrow2, hs02⟩ := hR2
  have hl1 : t1.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow1
  have hl1' : t1.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow1
  have hl2 : t2.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow2
  have hl2' : t2.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow2
  have hlat : Submodule.IsLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.1
  have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
  have hL0 : IsLift t0.lam t0.frame := t0.rep.2.2.2.2.1
  have hL1 : IsLift t0.lam t1.frame := by rw [← hl1]; exact t1.rep.2.2.2.2.1
  have hL2 : IsLift t0.lam t2.frame := by rw [← hl2]; exact t2.rep.2.2.2.2.1
  have hG0 := G_ne_of_Gt Y h0
  have hG1 := G_ne_of_Gt Y h1
  have hG2 := G_ne_of_Gt Y h2
  have hTh1 : Th t0.lam (lf D (X.Fu u)) t0.frame t1.frame (t1.lin * t0.lin⁻¹) = Hp t0.lam (lf D (X.Fu u)) t0.frame := by
    have h : Formalism.L2.SG.TermOp.s0T t0 t1 = 1 := hs01
    unfold Formalism.L2.SG.TermOp.s0T at h
    rw [if_pos ⟨hl1.symm, hl1'.symm⟩] at h
    exact (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam hlat _ t0.frame t1.frame _ hLF hL0 hG0).1 h
  have hTh2 : Th t0.lam (lf D (X.Fu u)) t0.frame t2.frame (t2.lin * t0.lin⁻¹) = Hp t0.lam (lf D (X.Fu u)) t0.frame := by
    have h : Formalism.L2.SG.TermOp.s0T t0 t2 = 1 := hs02
    unfold Formalism.L2.SG.TermOp.s0T at h
    rw [if_pos ⟨hl2.symm, hl2'.symm⟩] at h
    exact (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam hlat _ t0.frame t2.frame _ hLF hL0 hG0).1 h
  have hsym1 := CorankRelation.Th_symm D.R.k hdim t0.lam hlat _ t0.frame t1.frame (t1.lin * t0.lin⁻¹) hLF hL0 hL1 hG0 hG1
    (CorankRelation.frame_mem_iff t0 t1) hTh1
  rw [show (t1.lin * t0.lin⁻¹)⁻¹ = t0.lin * t1.lin⁻¹ by group] at hsym1
  have htr := CorankRelation.Th_trans t0.lam _ t1.frame t0.frame t2.frame (t0.lin * t1.lin⁻¹) (t2.lin * t0.lin⁻¹)
    (fun x hx => (CorankRelation.frame_mem_iff t0 t2 x).1 hx) hsym1 hTh2
  rw [show (t2.lin * t0.lin⁻¹) * (t0.lin * t1.lin⁻¹) = t2.lin * t1.lin⁻¹ by group] at htr
  have hsym2 := CorankRelation.Th_symm D.R.k hdim t0.lam hlat _ t1.frame t2.frame (t2.lin * t1.lin⁻¹) hLF hL1 hL2 hG1 hG2
    (CorankRelation.frame_mem_iff t1 t2) htr
  rw [show (t2.lin * t1.lin⁻¹)⁻¹ = t1.lin * t2.lin⁻¹ by group] at hsym2
  exact ⟨hl1, hl2, hsym2⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
