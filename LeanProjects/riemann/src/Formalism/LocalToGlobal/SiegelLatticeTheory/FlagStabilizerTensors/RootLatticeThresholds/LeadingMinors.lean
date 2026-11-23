import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

namespace Formalism.L2.SG.LeadingMinorsNonvanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leading_minor_ne_zero {D : D7} {T T' : ℕ} (hT : 0 < T) (F : LFlag (hS D) D.R.rS (T : D.host.E))
    (F' : LFlag (hS D) D.R.rS (T' : D.host.E)) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hG : Gval F F' ≠ 0) :
    Dr1 F F' ≠ 0 := by
  intro h0
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have h1 := (b_G_pos (p_starConj D) hT F F' hz hz' hG (p_posX D T hT F) τ).1
  rw [b_tauG (p_starConj D) F F' τ, h0, map_zero, norm_zero, Complex.ofReal_re] at h1
  have h2 : (0:ℝ) ≤ (T:ℝ) * T' * ‖τ (Dr F F')‖ ^ 2 := by positivity
  nlinarith

theorem atSomeAll_holds : Formalism.L2.SG.TermTieOf.AtSomeAll := by
  intro D X Y u u' t hG hrel
  obtain ⟨F', ⟨hP, hmk⟩, hR⟩ := hrel
  have hf := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) _ ((Y.rowsOK u).1 t.lam t.mem)
  have hGv : Gval (lf D (X.Fu u)) F' ≠ 0 := by
    have e := Formalism.L2.SG.TermDef.Gt_mk hf.1 ⟨F', hP⟩
    rw [hmk] at e
    exact fun h0 => hG (e.trans h0)
  have hTu := tie_Tu_pos D u
  have hTu' := tie_Tu_pos D u'
  have hDr1 : Dl (lf D (X.Fu u)).fl F'.fl (D.R.rS + 1) ≠ 0 :=
    leading_minor_ne_zero hTu (lf D (X.Fu u)) F' rfl hP.1.2 hGv
  have geo := cell_geom D.host.F D.host.E (hS D) D.R.rS _ _ (lf D (X.Fu u)).fl F'.fl (tie_trace D.sp.cm)
    (tie_aniso D _ hTu (lf D (X.Fu u))) (tie_aniso D _ hTu' F') hR
  obtain ⟨p, hp⟩ := cell_of_matRel cell_inv cell_sign cell_bruhat cell_mono cell_point (le_refl (D.R.rS + 1))
    ((Zhat (lf D (X.Fu u)).fl F'.fl).submatrix (Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castLE (le_refl (D.R.rS + 1))))
    (by rw [← tie_Dl_eq']; exact hDr1) (geo (D.R.rS + 1) le_rfl (Or.inr ⟨rfl, hGv⟩))
  refine ⟨p, F', ⟨hP, hmk⟩, hGv, ?_⟩
  obtain ⟨L, U, hL, hU, hZ⟩ := hp
  refine ⟨L, U, hL, hU, ?_⟩
  rw [← hZ]
  funext a b
  first
  | rfl
  | (simp [ZhatOM, ZhatL, Matrix.submatrix_apply]; rfl)

end Formalism.L2.SG.LeadingMinorsNonvanishing

end
