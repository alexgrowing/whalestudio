import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfB
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SpanSubtraction
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.UnitriangularCharts
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KronHolPsiInterpInterpC
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeOfDet
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BasePsiLeviLowerBound
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology Asymptotics Filter Metric
open scoped ENNReal
open GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction

namespace GlobalTheory.DivisionVolume

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Local

variable {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa)

end Local

section Hyp

variable {X : Data E r}

open Classical in

def unitVec (e : Ent X) : Fin (nd X) → ℂ := fun k => if (Fintype.equivFin (Ent X)).symm k = e then 1 else 0

open NumberField in
open MeasureTheory Topology Asymptotics Filter Metric in
open scoped ENNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma norm_dmin_cpt_last_eq_one {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0)
    (w : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ (Fin.last r)‖ = 1 := by
  rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.dmin_cpt_orth X hx0, _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor_last]
  have hN : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X w) τ).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat]
    · intro a b hab
      have h' : a < b := hab
      simp [_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, not_lt.2 h'.le, h'.ne]
  have h0 := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_lminor_zero X τ (Fin.last r)
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor_last, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Gw_zero] at h0
  have hmap : ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X w) τ).map (starRingEnd ℂ)).det = 1 := by
    have h := RingHom.map_det (starRingEnd ℂ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X w) τ)
    rw [hN, map_one] at h
    exact h.symm
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Gw
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hN, hmap, one_mul, mul_one, h0]

open NumberField in
open MeasureTheory Topology Asymptotics Filter Metric in
open scoped ENNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma sum_range_odd_mul_sub_eq (L : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ Finset.range r, (2 * (i : ℝ) + 1) * (L (i + 1) - L i) =
      (2 * (r : ℝ) - 1) * L r + L 0 - 2 * ∑ i ∈ Finset.range r, L i := by
  induction r with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

open NumberField in
open MeasureTheory Topology Asymptotics Filter Metric in
open scoped ENNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma sum_range_centered_mul_sub_eq (L : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ Finset.range r, (2 * (i : ℝ) - ((r : ℝ) - 1)) * (L (i + 1) - L i) =
      -2 * ∑ i ∈ Finset.range r, L i + ((r : ℝ) - 1) * L r + ((r : ℝ) + 1) * L 0 := by
  have h1 := sum_range_odd_mul_sub_eq L r
  have h2 : ∑ i ∈ Finset.range r, (L (i + 1) - L i) = L r - L 0 := Finset.sum_range_sub L r
  have h3 : ∑ i ∈ Finset.range r, (2 * (i : ℝ) - ((r : ℝ) - 1)) * (L (i + 1) - L i) =
      ∑ i ∈ Finset.range r, (2 * (i : ℝ) + 1) * (L (i + 1) - L i) -
        (r : ℝ) * ∑ i ∈ Finset.range r, (L (i + 1) - L i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h3, h1, h2]
  ring

open NumberField in
open MeasureTheory Topology Asymptotics Filter Metric in
open scoped ENNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma phla_kapW_cpt_eq_log_densF {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) {w : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)} (hw : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w ∈ X.dom) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X) (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) = Real.log (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 w) := by
  have hne : ∀ τ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ i ≠ 0 := fun τ i => _root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.dmin_ne X hw τ i
  have hpos : ∀ τ i, 0 < ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ i‖ :=
    fun τ i => norm_pos_iff.2 (hne τ i)
  have hzero : ∀ τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ 0 = 1 := fun τ => by
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.dmin_prod X hw]
    exact Finset.prod_eq_one fun j _ => absurd j.isLt (by simp)
  let L : X.Ψ → ℕ → ℝ := fun τ k =>
    if h : k < r + 1 then Real.log ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ ⟨k, h⟩‖ else 0
  have hL : ∀ τ (i : Fin (r + 1)), Real.log ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ i‖ = L τ i := by
    intro τ i
    simp only [L, dif_pos i.isLt, Fin.eta]
  have hL0 : ∀ τ, L τ 0 = 0 := fun τ => by
    simp [L, hzero]
  have hLr : ∀ τ, L τ r = 0 := fun τ => by
    have := norm_dmin_cpt_last_eq_one hx0 w τ
    simp only [L, lt_add_one, dite_true]
    rw [show (⟨r, lt_add_one r⟩ : Fin (r + 1)) = Fin.last r from rfl, this, Real.log_one]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos
      (by rw [norm_div]; exact div_pos (hpos _ _) (hpos _ _)) _).ne'),
    Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => zpow_pos (hpos _ _) _).ne')]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos
      (by rw [norm_div]; exact div_pos (hpos _ _) (hpos _ _)) _).ne'),
    Real.log_prod (fun i _ => (zpow_pos (hpos _ _) _).ne')]
  simp only [Real.log_zpow, norm_div]
  rw [Finset.mul_sum]
  have hterm : ∀ i : Fin r, -2 * Real.log ((‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ i.succ‖ /
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ i.castSucc‖) ^
        (-((2 * ((i : ℕ) : ℤ) - ((r : ℤ) - 1) : ℤ) : ℝ) / 2)) =
      (2 * ((i : ℕ) : ℝ) - ((r : ℝ) - 1)) * (L τ ((i : ℕ) + 1) - L τ (i : ℕ)) := by
    intro i
    rw [Real.log_rpow (div_pos (hpos _ _) (hpos _ _)), Real.log_div (hpos _ _).ne' (hpos _ _).ne',
      hL, hL]
    simp only [Fin.val_succ, Fin.coe_castSucc]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  have hterm2 : ∀ i : Fin r,
      ((-2 : ℤ) : ℝ) * Real.log ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ i.castSucc‖ =
        -2 * L τ (i : ℕ) := by
    intro i
    rw [hL]
    simp
  rw [Finset.sum_congr rfl fun i _ => hterm2 i]
  rw [Fin.sum_univ_eq_sum_range (fun i => (2 * (i : ℝ) - ((r : ℝ) - 1)) * (L τ (i + 1) - L τ i)),
    Fin.sum_univ_eq_sum_range (fun i => -2 * L τ i), sum_range_centered_mul_sub_eq, hL0, hLr,
    ← Finset.mul_sum]
  ring

open NumberField in
open MeasureTheory Topology Asymptotics Filter Metric in
open scoped ENNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma leviWeight_sub_leviDensity_eq_lemma {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)} (hz : z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0)
    (ξ : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviO X x0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la) z ξ - _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviDens X x0 z ξ =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X x0 (la - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X) z ξ := by
  have hlin := _root_.GlobalTheory.FrameThetaCompare.curv_lin X (x0 := x0) (z := z) hz 1 (-1) la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X) ξ
  rw [one_smul, neg_one_smul, ← sub_eq_add_neg] at hlin
  rw [hlin]
  have h1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X x0 la z ξ = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviO X x0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la) z ξ := rfl
  have h2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X x0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X) z ξ = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviDens X x0 z ξ := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.lev _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviDens
    congr 1
    refine _root_.ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ
    filter_upwards [(_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.isOpen_OmF X x0).mem_nhds hz] with y hy
    rw [phla_kapW_cpt_eq_log_densF hx0 hy]
  rw [h1, h2]
  push_cast
  ring

open NumberField in
open MeasureTheory Topology Asymptotics Filter Metric in
open scoped ENNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma sum_mul_norm_unitVec_sq_eq (c : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X → ℝ) (e : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) :
    ∑ e', c e' * ‖_root_.GlobalTheory.DivisionVolume.unitVec e ((Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X)) e')‖ ^ 2 = c e := by
  classical
  rw [Finset.sum_eq_single e]
  · simp [_root_.GlobalTheory.DivisionVolume.unitVec]
  · intro b _ hb
    simp [_root_.GlobalTheory.DivisionVolume.unitVec, hb]
  · intro h
    exact absurd (Finset.mem_univ e) h

open NumberField in
open MeasureTheory Topology Asymptotics Filter Metric in
open scoped ENNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.DivisionVolume.margin_iff (h0 : 0 < X.p0) (h1 : X.p0 < r)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (m : ℝ) :
    (∀ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ∀ z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0, ∀ ξ : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ,
      m * _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviRh X x0 z ξ ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviO X x0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la) z ξ - _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviDens X x0 z ξ) ↔
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.GapsPairing X (la - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X) m := by
  constructor
  · intro H τ
    have hx0 := _root_.GlobalTheory.OrthNear.isOrth_x0F X
    have h0mem : (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X) := by
      obtain ⟨R, hR, hb⟩ := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.good_ball X la
      have := hb 0 (Metric.mem_ball_self hR)
      exact _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.cpt_mem_dom X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.orth_mem_dom X hx0) hx0 this.1 this.2.1
    have key : ∀ e : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X,
        m * (_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑(↑e.2 : Fin r × Fin r).1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑(↑e.2 : Fin r × Fin r).2 *
          ((_root_.GlobalTheory.CurvMargin.blockWt X e.1 (↑e.2 : Fin r × Fin r).2 : ℝ) -
            (_root_.GlobalTheory.CurvMargin.blockWt X e.1 (↑e.2 : Fin r × Fin r).1 : ℝ))) ≤
        _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑(↑e.2 : Fin r × Fin r).1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑(↑e.2 : Fin r × Fin r).2 *
          (((la - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X) e.1 (↑e.2 : Fin r × Fin r).2 : ℝ) -
            ((la - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X) e.1 (↑e.2 : Fin r × Fin r).1 : ℝ)) := by
      intro e
      have h := H _ hx0 0 h0mem (_root_.GlobalTheory.DivisionVolume.unitVec e)
      rw [leviWeight_sub_leviDensity_eq_lemma hx0 la h0mem,
        _root_.GlobalTheory.CurvMargin.leviRh_eq X _ hx0 h0mem] at h
      have hR : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X) (la - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X) 0
          (_root_.GlobalTheory.DivisionVolume.unitVec e) =
          _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviM X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X (la - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X)) (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X) 0 (_root_.GlobalTheory.DivisionVolume.unitVec e) :=
        rfl
      rw [hR, _root_.GlobalTheory.LeviZero.leviZero r X _ _ hx0,
        _root_.GlobalTheory.LeviZero.leviZero r X _ _ hx0] at h
      simp only [sum_mul_norm_unitVec_sq_eq] at h
      exact h
    refine ⟨fun i j hij hjp => ?_, fun i0 i1 hi0 hi1 => ?_⟩
    · have hlt : i < j := Fin.lt_iff_val_lt_val.2 (by omega)
      have h := key (τ, ⟨(j, i), hlt⟩)
      clear key H hx0 h0mem
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, _root_.GlobalTheory.CurvMargin.blockWt, Pi.sub_apply] at h
      by_cases hi : (i : ℕ) < X.p0
      · have hj : (j : ℕ) < X.p0 := by omega
        simp only [hi, hj, if_true] at h
        norm_num at h
        simp only [Pi.sub_apply]
        have h' : ((la τ j - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X τ j : ℤ) : ℝ) ≤ ((la τ i - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X τ i : ℤ) : ℝ) := by
          push_cast
          linarith
        exact_mod_cast h'
      · have hj : ¬ (j : ℕ) < X.p0 := by omega
        simp only [hi, hj, if_false] at h
        norm_num at h
        simp only [Pi.sub_apply]
        have h' : ((la τ j - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X τ j : ℤ) : ℝ) ≤ ((la τ i - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X τ i : ℤ) : ℝ) := by
          push_cast
          linarith
        exact_mod_cast h'
    · have hlt : i0 < i1 := Fin.lt_iff_val_lt_val.2 (by omega)
      have h := key (τ, ⟨(i1, i0), hlt⟩)
      clear key H hx0 h0mem
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, _root_.GlobalTheory.CurvMargin.blockWt, Pi.sub_apply] at h
      have hi0' : (i0 : ℕ) < X.p0 := by omega
      have hi1' : ¬ (i1 : ℕ) < X.p0 := by omega
      simp only [hi0', hi1', if_true, if_false] at h
      norm_num at h
      simp only [Pi.sub_apply, Int.cast_sub]
      linarith
  · intro hG x0 hx0 z hz ξ
    rw [leviWeight_sub_leviDensity_eq_lemma hx0 la hz ξ]
    refine _root_.GlobalTheory.FrameThetaCompare.margin_of_gaps X h0 (la - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X) m ?_ ?_ hx0 hz ξ
    · intro τ a b hab
      exact (hG τ).1 a b hab.1 hab.2
    · intro τ a b ha hb
      have h := (hG τ).2 a b ha (by omega)
      push_cast at h
      exact h

def LeviHyp (Xa : ArchInM X) : Prop :=
  PropDisc X ∧ FinMu X ∧
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) ∧
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) ∧
    (∀ P, X.IsBddSec (Xa.Fp + nd X • Xa.L) P → P ∈ X.SS (Xa.Fp + nd X • Xa.L)) ∧
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) ∧
    (∀ P, X.IsBddSec (Xa.Fp + Xa.T • Xa.L) P → P ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) ∧
    (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)

def WeightHyp (Xa : ArchInM X) : Prop :=
  PropDisc X ∧ FiniteVolume X ∧ FiniteDimCusp X (wtTop Xa) ∧
    ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧ GapsPairing X (Xa.Fp - kapW X) m

end Hyp

section Size

variable {X : Data E r}

def InV (Xa : ArchInM X) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF ∧
    ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
      (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤

end Size

def HasBasis {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) : Prop :=
  ∃ t : Fin Fl.δ → Frame X.Ψ r → ℂ, (∀ i, t i ∈ X.SS Xa.Fp) ∧ BasisOnS Fl t

def SubtractWide (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (t : Fin Fl.δ → Frame X.Ψ r → ℂ),
    (∀ i, X.IsSec Xa.Fp (t i)) → BasisOnS Fl t →
    ∀ f, X.IsSec (wtTop Xa) f →
      ∃ cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ,
        VanOrd Fl (Xa.T - nd X) fun x => f x - lead Fl t cc x

def DivisionWide (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), LeviHyp Xa → HasBasis Fl →
    ∀ f ∈ X.SS (wtTop Xa), InV Xa f → VanOrd Fl (Xa.T - nd X) f →
      ∃ h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ,
        (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), h α ∈ X.SS (wtLow Xa)) ∧
        ∀ x ∈ X.dom, f x = tail Fl h x

def DivisionWithBasis (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), DivHyp Xa → HasBasis Fl →
    ∀ f ∈ X.SS (wtTop Xa), BddByPow Xa f → VanOrd Fl (Xa.T - nd X) f →
      ∃ h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ,
        (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), h α ∈ X.SS (wtLow Xa)) ∧
        ∀ x ∈ X.dom, f x = tail Fl h x

def SpanWide (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), LeviHyp Xa →
    ∀ t : Fin Fl.δ → Frame X.Ψ r → ℂ, (∀ i, t i ∈ X.SS Xa.Fp) → BasisOnS Fl t →
    ∀ f ∈ X.SS (wtTop Xa), InV Xa f → InSpan Fl t f

end

end GlobalTheory.DivisionVolume
