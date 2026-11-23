import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Torsor
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsX
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpStmt

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm.ClassAbs

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def AmpValLowerC : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
    s.toTerm.generic → s.toTerm.G ≠ 0 →
      c * (‖Formalism.L2.SG.PairVal.cTerm vR s.toTerm‖ *
          ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.toTerm))‖) ≤
        ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s)‖

theorem vec_norm_ge (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    Formalism.L2.SG.TermOp.wt s * ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s)‖ ≤
      ‖(Y.tO u u').vec s‖ := by
  have h := PiLp.norm_apply_le ((Y.tO u u').vec s) (⟨s.lam, s.mem⟩, ⟨s.lam', s.mem'⟩)
  have e : ((Y.tO u u').vec s) (⟨s.lam, s.mem⟩, ⟨s.lam', s.mem'⟩) =
      ((Formalism.L2.SG.TermOp.wt s : ℝ) : ℂ) •
        Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) := by
    change (Formalism.L2.SG.TermOp.vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) (⟨s.lam, s.mem⟩, ⟨s.lam', s.mem'⟩) = _
    simp [Formalism.L2.SG.TermOp.vec]
  rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ Formalism.L2.SG.TermOp.wt s from Real.sqrt_nonneg _)] at h
  exact h

theorem classAbsC_of
    (hAC : Formalism.L2.SG.TermOp.AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u'))
    (hA : AmpValLowerC X Y u u' vR i0 i0' νq) (hM : LiftMassC X Y u u') :
    ClassAbsC X Y u u' vR i0 i0' νq κ := by
  obtain ⟨c, hc, hA⟩ := hA
  have hv : Summable (fun s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') =>
      ‖(Y.tO u u').vec s‖) := hAC.2.1
  intro ρ
  refine Formalism.L2.SG.RowsAbsX.summable_of_fibre_bound
    (fun (t : ClassT X Y u u' κ ρ) (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) =>
      s.toTerm = t.1)
    (fun p p' s hp hp' => Subtype.ext (hp.symm.trans hp'))
    (fun s => c⁻¹ * ‖(Y.tO u u').vec s‖) (fun s => mul_nonneg (inv_nonneg.2 hc.le) (norm_nonneg _))
    (hv.mul_left _) _ (fun _ => norm_nonneg _) ?_
  intro t
  rw [tsum_mul_left]
  set A : ℝ := ‖Formalism.L2.SG.PairVal.cTerm vR t.1‖ *
    ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf t.1))‖ with hAdef
  have hA0 : 0 ≤ A := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hF : ‖(((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cTerm vR t.1) •
      Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf t.1))‖ =
      Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) * A := by
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hAdef, mul_assoc]
  rw [hF]
  have hw0 : ∀ s : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // s.toTerm = t.1},
      0 ≤ Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' := fun s => inv_nonneg.2 (Nat.cast_nonneg _)
  have hsum := hM t.1 t.2.1
  have hws : Summable (fun s : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') //
      s.toTerm = t.1} => Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam') := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at hsum
    exact zero_ne_one hsum
  have hw1 : ∀ s : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // s.toTerm = t.1},
      Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' ≤ 1 := by
    intro s
    rw [← hsum]
    exact hws.le_tsum s (fun j _ => hw0 j)
  have hvf : Summable (fun s : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') //
      s.toTerm = t.1} => ‖(Y.tO u u').vec s.1‖) := hv.subtype _
  have key : ∀ s : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // s.toTerm = t.1},
      c * (Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) * A) * Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' ≤
        ‖(Y.tO u u').vec s.1‖ := by
    intro s
    obtain ⟨s, hs⟩ := s
    have hgen : s.toTerm.generic := hs ▸ t.2.1.1
    have hG : s.toTerm.G ≠ 0 := hs ▸ t.2.1.2
    have h1 := hA s hgen hG
    rw [hs] at h1
    have hlam : s.lam = t.1.lam := congrArg Term.lam hs
    have h2 := vec_norm_ge X Y u u' s
    have hwt : Formalism.L2.SG.TermOp.wt s =
        Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) * Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') s.lam') := by
      unfold Formalism.L2.SG.TermOp.wt
      rw [← hlam]
      exact Real.sqrt_mul (inv_nonneg.2 (Nat.cast_nonneg _)) _
    have hsq : Formalism.MainNotions.S.wRow D (X.Fu u') s.lam' ≤ Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') s.lam') := by
      have h0 : 0 ≤ Formalism.MainNotions.S.wRow D (X.Fu u') s.lam' := inv_nonneg.2 (Nat.cast_nonneg _)
      have h1' : Formalism.MainNotions.S.wRow D (X.Fu u') s.lam' ≤ 1 := hw1 ⟨s, hs⟩
      calc Formalism.MainNotions.S.wRow D (X.Fu u') s.lam'
          = Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') s.lam') * Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') s.lam') :=
            (Real.mul_self_sqrt h0).symm
        _ ≤ Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') s.lam') * 1 :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_one.2 h1') (Real.sqrt_nonneg _)
        _ = _ := mul_one _
    rw [hwt] at h2
    have hS0 : 0 ≤ Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) := Real.sqrt_nonneg _
    have hS1 : 0 ≤ Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') s.lam') := Real.sqrt_nonneg _
    calc c * (Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) * A) * Formalism.MainNotions.S.wRow D (X.Fu u') s.lam'
        ≤ c * (Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) * A) * Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') s.lam') :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hc.le (mul_nonneg hS0 hA0))
      _ = Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) * Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') s.lam') * (c * A) := by ring
      _ ≤ Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) t.1.lam) * Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') s.lam') *
            ‖Formalism.L2.SG.PackageTie.hsEmb (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s)‖ :=
          mul_le_mul_of_nonneg_left (by rw [hAdef]; exact h1) (mul_nonneg hS0 hS1)
      _ ≤ _ := h2
  have hle := Summable.tsum_le_tsum key (hws.mul_left _) hvf
  rw [tsum_mul_left, hsum, mul_one] at hle
  rw [le_inv_mul_iff₀ hc]
  exact hle

end Formalism.L2.SG.Pf.RowForm.ClassAbs
