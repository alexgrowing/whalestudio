import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsAmp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsPt

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem rowsSum_of_val (vR : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (κ : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) (nc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hA : (Y.tO u u').AbsConv)
    (hL : TermOp.LiftOnto X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hAV : Formalism.L2.SG.Pf.RowForm.ClassAbs.AmpValLowerC X Y u u' vR i0 i0' νq)
    (hAF : PairVal.AutFin D (X.Fu u) (Y.what₂ u)) (hAF' : PairVal.AutFin D (X.Fu u') (Y.what₂ u')) (hnc : 0 < nc) :
    DataInst.RowsSum vR κ nc (RealObj.VtPt X u u' 1 i0 i0' FdN FdN' νq) := by
  intro ρ
  obtain ⟨c, hc, hcv⟩ := hAV
  obtain ⟨C, hC⟩ := Formalism.L2.SG.WConst.weightBound_holds X Y u u' hnc
  obtain ⟨m, hm0, hmle⟩ := Formalism.L2.SG.RowsAbsX.exists_wRow_lb u (X.Fu u) (Y.what₂ u) hAF
  obtain ⟨m', hm0', hmle'⟩ := Formalism.L2.SG.RowsAbsX.exists_wRow_lb u' (X.Fu u') (Y.what₂ u') hAF'
  have hwm : 0 < Real.sqrt (m * m') := Real.sqrt_pos.2 (mul_pos hm0 hm0')
  have hcw : 0 < c * Real.sqrt (m * m') := mul_pos hc hwm
  let Mm : ℝ := ∑ Λ ∈ Y.what₂ u, |PairVal.massRow D (X.Fu u) (Y.what₂ u) Λ|
  let τ : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') :=
    fun t => (hL t).choose
  have hτ : ∀ t, (τ t).toTerm = t := fun t => (hL t).choose_spec
  have hτi : Function.Injective τ := fun a b h => by rw [← hτ a, ← hτ b, h]
  let C' : ℝ := max C 0
  have hC'0 : 0 ≤ C' := le_max_right _ _
  let K0 : ℝ := C' * Real.sqrt Mm / (c * Real.sqrt (m * m'))
  have hK0n : 0 ≤ K0 := div_nonneg (mul_nonneg hC'0 (Real.sqrt_nonneg _)) hcw.le
  let g : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ := fun t => K0 * ‖(Y.tO u u').vec (τ t)‖
  have hg0 : ∀ t, 0 ≤ g t := fun t => mul_nonneg hK0n (norm_nonneg _)
  have hg : Summable g := (hA.2.1.comp_injective hτi).mul_left K0
  let A : TB.Pt D.host.E → TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → Prop := fun p t =>
    DataInst.Elig t ∧ κ t = ρ ∧ ∃ w, DataInst.ptOfList (D.R.rS + 1) p = some w ∧ t.atPt w
  have hAu : ∀ p p' t, A p t → A p' t → p = p' := by
    rintro p p' t ⟨-, -, w, hw, ht⟩ ⟨-, -, w', hw', ht'⟩
    obtain rfl := Formalism.L2.SG.RowsAbsX.ptUniq_holds X Y u u' t w w' ht ht'
    exact ptOfList_inj hw hw'
  refine summable_of_fibre_bound A hAu g hg0 hg _ (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  intro p
  have hS0 : 0 ≤ ∑' t : {t // A p t}, g t := tsum_nonneg fun t => hg0 t
  rcases hp : DataInst.ptOfList (D.R.rS + 1) p with _ | w
  · have h0 : DataInst.rowVec (vR) κ nc ρ p = 0 := by
      simp [DataInst.rowVec, hp]
    rw [h0, norm_zero, zero_mul]
    exact hS0

  have hA' : ∀ t, A p t ↔ (DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w) := by
    intro t
    simp only [A, hp, Option.some.injEq, exists_eq_left']
  let Sw := {t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) // DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}
  have hsum : ∑' t : {t // A p t}, g t = ∑' t : Sw, g t.1 := by
    rw [← (Equiv.subtypeEquivRight hA').tsum_eq (fun t : Sw => g t.1)]
    rfl
  rw [hsum]
  have hgS : Summable (fun t : Sw => g t.1) := hg.comp_injective Subtype.val_injective
  let f : Sw → ℂ := fun t =>
    ((Real.sqrt (PairVal.massTerm t.1) : ℝ) : ℂ) * PairVal.cAt (vR) t.1 w
  let Dn : ℝ := Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T w) * DataInst.phi (D.R.rS + 1) p
  let V : ℝ := ‖PackageTie.hsEmb (RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w)‖
  let N : ℝ := Real.sqrt (RealObj.nW X u u' w)
  have hrow : DataInst.rowVec (vR) κ nc ρ p = (∑' t : Sw, f t) / (Dn : ℂ) := by
    simp only [DataInst.rowVec, hp]
    rfl
  have hvt : RealObj.VtPt X u u' 1 i0 i0' FdN FdN' νq p =
      ((N : ℝ) : ℂ) • PackageTie.hsEmb (RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w) := by
    simp only [RealObj.VtPt, RealObj.ptOfL, hp] <;> rfl
  have hnv : ‖RealObj.VtPt X u u' 1 i0 i0' FdN FdN' νq p‖ = N * V := by
    rw [hvt, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hnr : ‖DataInst.rowVec (vR) κ nc ρ p‖ = ‖∑' t : Sw, f t‖ / |Dn| := by
    rw [hrow, norm_div, Complex.norm_real, Real.norm_eq_abs]
  rw [hnv, hnr]
  have hgS0 : 0 ≤ ∑' t : Sw, g t.1 := tsum_nonneg fun t => hg0 t.1

  by_cases hreal : ∃ γ, RealObj.IsPtRep X u u' w γ
  swap
  · have hV : V = 0 := by
      have : RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w = 0 := by simp [RealObj.unscaledOperatorAtPointRepresentative, hreal]
      simp only [V, this, map_zero, norm_zero]
    rw [hV, mul_zero, mul_zero]
    exact hgS0

  by_cases hne : Nonempty Sw
  swap
  · haveI : IsEmpty Sw := not_nonempty_iff.1 hne
    rw [tsum_empty, norm_zero, zero_div, zero_mul]
    exact hgS0
  obtain ⟨t0⟩ := hne
  have hNC : N ≤ C' * |Dn| :=
    (hC p w hp hreal ⟨t0.1, t0.2.1.2, t0.2.2.2⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

  have hterm : ∀ t : Sw, ‖f t‖ * (C' * V) ≤ g t.1 := by
    intro t
    have hat : t.1.atPt w := t.2.2.2
    have huq : ∀ w₁ w₂, t.1.atPt w₁ → t.1.atPt w₂ → w₁ = w₂ :=
      fun w₁ w₂ h h' => Formalism.L2.SG.RowsAbsX.atPt_uniq _ _ _ t.1.cls w₁ w₂ h h'
    have hpt : PairVal.ptOf t.1 = w := by
      have hrel := Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' (X.Fu u) (Y.what₂ u) t.1 w hat
      exact huq _ _ (PairVal.ptOf_spec t.1 ⟨w, hat, hrel⟩) hat
    have hcT : PairVal.cTerm vR t.1 = PairVal.cAt vR t.1 w :=
      PairVal.cTerm_of_atPt vR t.1 hat (fun w' h' => huq w' w h' hat)
    have h1 := hcv (τ t.1) (by rw [hτ]; exact t.2.1.1) (by rw [hτ]; exact t.2.1.2)
    rw [hτ, hpt, hcT] at h1
    have h2 := Formalism.L2.SG.Pf.RowForm.ClassAbs.vec_norm_ge X Y u u' (τ t.1)
    have hwt : Real.sqrt (m * m') ≤ Formalism.L2.SG.TermOp.wt (τ t.1) := by
      unfold Formalism.L2.SG.TermOp.wt
      exact Real.sqrt_le_sqrt (mul_le_mul (hmle _ (τ t.1).mem) (hmle' _ (τ t.1).mem') hm0'.le
        (hm0.le.trans (hmle _ (τ t.1).mem)))
    have hm : Real.sqrt (PairVal.massTerm t.1) ≤ Real.sqrt Mm := Real.sqrt_le_sqrt (massTerm_le t.1)
    have hf : ‖f t‖ = Real.sqrt (PairVal.massTerm t.1) * ‖PairVal.cAt vR t.1 w‖ := by
      simp only [f]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hV0 : 0 ≤ V := norm_nonneg _
    have hamp0 : 0 ≤ ‖PackageTie.hsEmb (TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (τ t.1))‖ := norm_nonneg _
    have e3 : ‖PairVal.cAt vR t.1 w‖ * V ≤ ‖(Y.tO u u').vec (τ t.1)‖ / (c * Real.sqrt (m * m')) := by
      rw [le_div_iff₀ hcw]
      have k1 : Real.sqrt (m * m') * ‖PackageTie.hsEmb (TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (τ t.1))‖ ≤
          ‖(Y.tO u u').vec (τ t.1)‖ := (mul_le_mul_of_nonneg_right hwt hamp0).trans h2
      nlinarith [mul_le_mul_of_nonneg_left h1 hwm.le]
    have e4 : 0 ≤ ‖PairVal.cAt (vR) t.1 w‖ * V :=
      mul_nonneg (norm_nonneg _) hV0
    calc ‖f t‖ * (C' * V)
        = C' * (Real.sqrt (PairVal.massTerm t.1) *
            (‖PairVal.cAt (vR) t.1 w‖ * V)) := by rw [hf]; ring
      _ ≤ C' * (Real.sqrt Mm * (‖(Y.tO u u').vec (τ t.1)‖ / (c * Real.sqrt (m * m')))) := by
          apply mul_le_mul_of_nonneg_left _ hC'0
          exact mul_le_mul hm e3 e4 (Real.sqrt_nonneg _)
      _ = g t.1 := by simp only [g, K0]; ring

  have hlhs : ‖∑' t : Sw, f t‖ / |Dn| * (N * V) ≤ ‖∑' t : Sw, f t‖ * (C' * V) := by
    rcases (abs_nonneg Dn).eq_or_lt with hD | hD
    · rw [← hD, div_zero, zero_mul]
      exact mul_nonneg (norm_nonneg _) (mul_nonneg hC'0 (norm_nonneg _))
    · rw [div_mul_eq_mul_div, div_le_iff₀ hD]
      have : N * V ≤ C' * |Dn| * V := mul_le_mul_of_nonneg_right hNC (norm_nonneg _)
      calc ‖∑' t : Sw, f t‖ * (N * V) ≤ ‖∑' t : Sw, f t‖ * (C' * |Dn| * V) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = ‖∑' t : Sw, f t‖ * (C' * V) * |Dn| := by ring
  refine hlhs.trans ?_
  rcases (mul_nonneg hC'0 (norm_nonneg _) : 0 ≤ C' * V).eq_or_lt with hK | hK
  · rw [← hK, mul_zero]
    exact hgS0
  · have hfb : ∀ t : Sw, ‖f t‖ ≤ g t.1 / (C' * V) := fun t => by
      rw [le_div_iff₀ hK]; exact hterm t
    have hsn : Summable (fun t : Sw => ‖f t‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hfb (hgS.div_const _)
    calc ‖∑' t : Sw, f t‖ * (C' * V) ≤ (∑' t : Sw, ‖f t‖) * (C' * V) :=
          mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsn) hK.le
      _ = ∑' t : Sw, ‖f t‖ * (C' * V) := (tsum_mul_right).symm
      _ ≤ ∑' t : Sw, g t.1 := Summable.tsum_le_tsum hterm (hsn.mul_right _) hgS

end Formalism.L2.SG.RowsAbsX
