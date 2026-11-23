import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AbsNormTG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorEqPointMinor
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Term

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem frames_mem (t : TauC Y u u') :
    (∀ b, (X.Fu u).fvec b ∈ t.lam) ∧ (∀ b, t.frame.fl.fvec b ∈ t.lam) := by
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hP := t.rep.2.2.2.2
  exact ⟨Formalism.L2.SG.NGCut.PtPf.frame_mem (lf D (X.Fu u)) hrow.2.1.2.2.1.1 hrow.2.2,
    Formalism.L2.SG.NGCut.PtPf.frame_mem t.frame hP.1.1 hP.2.2.2⟩

theorem yT_mem (t : TauC Y u u') : NormalVectorPairings.yT Y u u' t ∈ t.lam := by
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  obtain ⟨h1, h2⟩ := frames_mem Y t
  exact yv_mem hrow.2.1.2.1 (Tu D u) (X.Fu u) t.frame.fl h1 h2

theorem yT'_mem (t : TauC Y u u') : NormalVectorPairings.yT' Y u u' t ∈ t.lam' := by
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  obtain ⟨h1, h2⟩ := frames_mem Y t
  have hv : NormalVectorPairings.yv t.frame.fl (X.Fu u) ∈ t.lam := yv_mem hrow.2.1.2.1 (Tu D u') t.frame.fl (X.Fu u) h2 h1
  have hg : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  rw [← hg] at hv
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 hv
  show t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u)) ∈ t.lam'
  rw [← hwv]
  simpa using hw

theorem yT'_orth (t : TauC Y u u') : ∀ x ∈ (X.Fu u').X, brS (VS D) (NormalVectorPairings.yT' Y u u' t) x = 0 := by
  intro x hx
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hlx : t.lin x ∈ (t.frame.fl).X := by
    have := (CorankRelation.mem_Xsp_mapLF (γ := t.lin) hiso (lf D (X.Fu u')) (t.lin x)).2 (by simpa using hx)
    exact this
  have h := yv_orth_X t.frame.fl (X.Fu u) (t.lin x) hlx
  show (VS D).hT x (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u))) = 0
  have e := hiso x (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u)))
  rw [LinearEquiv.apply_symm_apply] at e
  rw [← e]
  exact h

theorem yT'_self (t : TauC Y u u') :
    brS (VS D) (NormalVectorPairings.yT' Y u u' t) (NormalVectorPairings.yT' Y u u' t) =
      brS (VS D) (NormalVectorPairings.yv t.frame.fl (X.Fu u)) (NormalVectorPairings.yv t.frame.fl (X.Fu u)) := by
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  show (VS D).hT (t.lin.symm _) (t.lin.symm _) = _
  have e := hiso (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u))) (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u)))
  rw [LinearEquiv.apply_symm_apply] at e
  rw [← e]
  rfl

theorem lam_eq {t0 t : TauC Y u u'} (h : NormalVectorPairings.RelC Y u u' t0 t) : t.lam = t0.lam ∧ t.lam' = t0.lam' :=
  ⟨congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) h.1,
    congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) h.1⟩

end Term

theorem nmlInt_of
    (hLine : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t0 t : TauC Y u u'),
      Gt t0 ≠ 0 → Gt t ≠ 0 → NormalVectorPairings.RelC Y u u' t0 t → t.G = t0.G → 3 ≤ Tu D u → 3 ≤ Tu D u' →
        NormalVectorPairings.yT Y u u' t - NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0 ∈ (X.Fu u).X ∧
        NormalVectorPairings.yT' Y u u' t - NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0 ∈ (X.Fu u').X) :
    NormalVectorPairings.NmlInt := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hctx γ hNG t0 hGt0 hpt0 => ?_⟩
  have hT1 : (3 : ℕ) ≤ Tu D u := hctx.2.1.2.2.2.1
  have hT2 : (3 : ℕ) ≤ Tu D u' := hctx.2.1.2.2.2.2.1
  have hG := NormalVectorPairings.gval_occ Y t0 (by rw [hpt0]; exact hNG)
  rw [hpt0] at hG
  have hGeq : ∀ t : TauC Y u u', ptPN t = γ → t.G = t0.G := by
    intro t hpt
    have h1 := NormalVectorPairings.gval_occ Y t (by rw [hpt]; exact hNG)
    rw [hpt] at h1
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G Y t, Formalism.L2.SG.Pf.SatGram.gterm_G Y t0, h1, hG]
  have hGne := NormalVectorPairings.GPt_ne_of_NGPt _ _ hNG
  have hTne : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (show Tu D u ≠ 0 by omega)
  have hTne' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (show Tu D u' ≠ 0 by omega)

  have hrow := (Y.rowsOK u).1 t0.lam t0.mem
  have hun := hrow.2.1.2.1
  have hy0 := yT_mem Y t0
  obtain ⟨c0, hc0⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun hy0 hy0
  have hc0' : (c0 : D.host.E) = brS (VS D) (NormalVectorPairings.yT Y u u' t0) (NormalVectorPairings.yT Y u u' t0) := hc0
  have hval : brS (VS D) (NormalVectorPairings.yT Y u u' t0) (NormalVectorPairings.yT Y u u' t0) =
      ((Tu D u : ℕ) : D.host.E) * GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ := by
    show brS (VS D) (NormalVectorPairings.yv (X.Fu u) t0.frame.fl) (NormalVectorPairings.yv (X.Fu u) t0.frame.fl) = _
    rw [NormalVectorPairings.brS_yv_yv _ _ (by simp), ← hG]
    rfl
  have hc0ne : c0 ≠ 0 := by
    intro h
    have : (c0 : D.host.E) = 0 := by rw [h]; rfl
    rw [hc0', hval] at this
    exact mul_ne_zero hTne hGne this

  have hrow' := (Y.rowsOK u').1 t0.lam' t0.mem'
  have hun' := hrow'.2.1.2.1
  have hy1 := yT'_mem Y t0
  obtain ⟨c1, hc1⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun' hy1 hy1
  have hc1' : (c1 : D.host.E) = brS (VS D) (NormalVectorPairings.yT' Y u u' t0) (NormalVectorPairings.yT' Y u u' t0) := hc1
  have hval' : brS (VS D) (NormalVectorPairings.yT' Y u u' t0) (NormalVectorPairings.yT' Y u u' t0) =
      ((Tu D u' : ℕ) : D.host.E) * GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ := by
    rw [yT'_self, NormalVectorPairings.brS_yv_yv _ _ (by simp), NormalVectorPairings.Gflag_swap, ← hG]
  have hc1ne : c1 ≠ 0 := by
    intro h
    have : (c1 : D.host.E) = 0 := by rw [h]; rfl
    rw [hc1', hval'] at this
    exact mul_ne_zero hTne' hGne this
  refine ⟨Jfrac t0.lam (X.Fu u).X (NormalVectorPairings.yT Y u u' t0) hun (X_iso (X.Fu u)) (yv_orth_X (X.Fu u) t0.frame.fl)
      hy0 c0 hc0' hc0ne,
    Jfrac t0.lam' (X.Fu u').X (NormalVectorPairings.yT' Y u u' t0) hun' (X_iso (X.Fu u')) (yT'_orth Y t0) hy1 c1 hc1' hc1ne,
    Jfrac_ne_zero _ _ _ _ _ _ _ _ _ _, Jfrac_ne_zero _ _ _ _ _ _ _ _ _ _, fun t hGt hpt hrel => ⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨hl1, -⟩ := hLine D X Y u u' t0 t hGt0 hGt hrel (hGeq t hpt) hT1 hT2
    have hyt : NormalVectorPairings.yT Y u u' t ∈ t0.lam := (lam_eq Y hrel).1 ▸ yT_mem Y t
    show NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0 ∈ t0.lam ⊔ (X.Fu u).X.restrictScalars (𝓞 D.host.E)
    have e : NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0 =
        NormalVectorPairings.yT Y u u' t - (NormalVectorPairings.yT Y u u' t - NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0) := by
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hyt) (Submodule.mem_sup_right hl1)
  · obtain ⟨-, hl2⟩ := hLine D X Y u u' t0 t hGt0 hGt hrel (hGeq t hpt) hT1 hT2
    have hyt : NormalVectorPairings.yT' Y u u' t ∈ t0.lam' := (lam_eq Y hrel).2 ▸ yT'_mem Y t
    show NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0 ∈ t0.lam' ⊔ (X.Fu u').X.restrictScalars (𝓞 D.host.E)
    have e : NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0 =
        NormalVectorPairings.yT' Y u u' t - (NormalVectorPairings.yT' Y u u' t - NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0) := by
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hyt) (Submodule.mem_sup_right hl2)
  · have hb := norm_bound t0.lam (X.Fu u).X (NormalVectorPairings.yT Y u u' t0) hun (X_iso (X.Fu u))
      (yv_orth_X (X.Fu u) t0.frame.fl) hy0 c0 hc0' hc0ne
    rw [hc0', hval, abs_norm_TG] at hb
    unfold NormalInvariants.PG
    calc (1 : ℝ) ≤ _ := hb
      _ = _ := by ring
  · have hb := norm_bound t0.lam' (X.Fu u').X (NormalVectorPairings.yT' Y u u' t0) hun' (X_iso (X.Fu u'))
      (yT'_orth Y t0) hy1 c1 hc1' hc1ne
    rw [hc1', hval', abs_norm_TG] at hb
    unfold NormalInvariants.PG
    calc (1 : ℝ) ≤ _ := hb
      _ = _ := by ring

end Formalism.L2.SG.NGCut.NormalIntegrality
