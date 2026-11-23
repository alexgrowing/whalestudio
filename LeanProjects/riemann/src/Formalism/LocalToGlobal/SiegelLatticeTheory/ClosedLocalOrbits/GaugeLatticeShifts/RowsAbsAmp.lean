import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsX
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_wRow_lb {D : D7} (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hA : Formalism.L2.SG.PairVal.AutFin D F0 what₂) :
    ∃ m : ℝ, 0 < m ∧ ∀ Λ ∈ what₂, m ≤ wRow D F0 Λ := by
  rcases what₂.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · refine ⟨what₂.inf' h (wRow D F0), ?_, fun Λ hΛ => Finset.inf'_le _ hΛ⟩
    rw [Finset.lt_inf'_iff]
    exact fun Λ hΛ => Formalism.L2.SG.PairVal.wRow_pos D F0 (hA Λ hΛ)

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

theorem ampLower_of (hV : 0 < X.volK2) (hc : 0 < Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X X u (Y.FN u))
    (hc' : 0 < Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X X u' (Y.FN u'))
    (hA : Formalism.L2.SG.PairVal.AutFin D (X.Fu u) (Y.what₂ u)) (hA' : Formalism.L2.SG.PairVal.AutFin D (X.Fu u') (Y.what₂ u')) :
    AmpLower X Y u u' := by
  obtain ⟨m, hm, hmle⟩ := exists_wRow_lb u (X.Fu u) (Y.what₂ u) hA
  obtain ⟨m', hm', hmle'⟩ := exists_wRow_lb u' (X.Fu u') (Y.what₂ u') hA'
  have ha : 0 < Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 :=
    mul_pos (inv_pos.2 (Real.sqrt_pos.2 (mul_pos hc hc'))) hV
  refine ⟨Real.sqrt (m * m') * (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2),
    mul_pos (Real.sqrt_pos.2 (mul_pos hm hm')) ha, fun s => ?_⟩
  rw [Formalism.L2.SG.RowsConc.norm_vec Y s]
  have hχ : ∀ κ : X.B.I.Gf, ‖Formalism.L2.SG.TermOp.chiN X κ‖ = 1 := fun κ => by
    unfold Formalism.L2.SG.TermOp.chiN
    exact Formalism.L2.SG.TermOp.KExpCut.psiUnit X _
  have e : ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s)‖ =
      (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) *
        ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.OOt s)‖ := by
    unfold Formalism.L2.SG.TermOp.ampN
    rw [map_smul, map_smul, norm_smul, norm_smul, hχ, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  rw [e]
  have hw : Real.sqrt (m * m') ≤ Formalism.L2.SG.TermOp.wt s := by
    unfold Formalism.L2.SG.TermOp.wt
    exact Real.sqrt_le_sqrt (mul_le_mul (hmle _ s.mem) (hmle' _ s.mem') hm'.le (hm.le.trans (hmle _ s.mem)))
  have h0 : 0 ≤ (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) *
      ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.OOt s)‖ := mul_nonneg ha.le (norm_nonneg _)
  calc Real.sqrt (m * m') * (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) *
        ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.OOt s)‖
      = Real.sqrt (m * m') * ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) *
        ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.OOt s)‖) := by ring
    _ ≤ Formalism.L2.SG.TermOp.wt s * ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) *
        ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.OOt s)‖) := mul_le_mul_of_nonneg_right hw h0

end Formalism.L2.SG.RowsAbsX
