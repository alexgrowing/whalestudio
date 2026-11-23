import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceChartIndepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnExtTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcOfValuesEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernAtTwoEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfValuesMulOfValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagRationalSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.HermFrame GlobalTheory.SecForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped Classical ComplexOrder

namespace GlobalTheory.LineForm.DdcLine

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

def hseq (hX : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) :
    HermSeq (hX.atlas σ) 1 1 :=
  hX.seq (lineSC_shortExact fl) (h₁ := h.restrict (fl.isSubbundle 1) (fl.isVB 1)) (h₂ := h)
    (h₃ := VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1))
    (H.restrict _ _) H (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) _ _ _ H) σ

variable (hX : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2)

theorem crd_mem (x : (hX.atlas σ).Pt) : x.crd ∈ chartSet (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1 := by
  refine ⟨x.ch.map_source x.2, ?_⟩
  show (x.ch.symm x.crd) ∈ ptsIn p σ (frameAt fl x.pt).U
  rw [x.ch.left_inv x.2]
  exact mem_frameAt fl x.pt

theorem loc_omF (x : (hX.atlas σ).Pt) :
    (hX.atlas σ).loc (fld _ (omF hX σ h fl)) x.1.1 =ᶠ[𝓝 x.crd]
      fun v => (ofValues (extTrace (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1) v) : Alt D) := by
  filter_upwards [(isOpen_chartSet (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1).mem_nhds (crd_mem hX σ h H fl x)] with v hv
  have hv1 : v ∈ ((hX.atlas σ).e x.1.1).target := hv.1
  rw [HolAtlas.loc, dif_pos hv1]
  set y : (hX.atlas σ).Pt := ⟨(x.1.1, ((hX.atlas σ).e x.1.1).symm v), ((hX.atlas σ).e x.1.1).map_target hv1⟩ with hy
  have hb : v ∈ chartSet (hseq hX σ h H fl) (frameAt fl y.pt) x.1.1 := ⟨hv1, mem_frameAt fl y.pt⟩
  have e1 : y.crd = v := ((hX.atlas σ).e x.1.1).right_inv hv1
  change (ofValues (extTrace (midIn (hseq hX σ h H fl) (frameAt fl y.pt) x.1.1) y.crd) : Alt D) = _
  rw [e1, GlobalTheory.T.extTrace_chart_indep (hseq hX σ h H fl) (frameAt fl y.pt) (frameAt fl x.pt) x.1.1 ⟨hb, hv⟩]

end GlobalTheory.LineForm.DdcLine

namespace GlobalTheory.LineForm.DdcLine

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
variable (hX : IsRegVar p D) (σ : k →+* ℂ)

theorem c1F_det_metric_eq_chernOne {F : X.Modules} {r : ℕ} {m : VMetric p F r} (Hm : m.IsCInf) (x : (hX.atlas σ).Pt) (c : Chart F r)
    (hc : x.pt ∈ ptsIn p σ c.U) :
    c1F hX σ (VMetric.det Hm) x = ofValues (chernOne (fun w => (m.met σ).G c (x.ch.symm w)) x.crd) := by
  obtain ⟨⟨a, y⟩, hy⟩ := x
  have hy' : y ∈ a.e.source := hy
  change y ∈ ptsIn p σ c.U at hc
  set b := pick ((VMetric.det Hm).φ σ).isLB y
  have hb : y ∈ ptsIn p σ ((VMetric.det Hm).B.U b) := mem_pick _ y
  have hc' : y ∈ ptsIn p σ ((VMetric.det Hm).B.U c) := hc
  have ho := ChartGlue.isOpen_over a.e (isOpen_ptsIn (p := p) (σ := σ) ((VMetric.det Hm).B.U c ⊓ (VMetric.det Hm).B.U b))
  have hm := ChartGlue.mem_over a.e hy' (mem_ptsIn_inf.2 ⟨hc', hb⟩)
  set u := c.isFrame.detUnit b.isFrame inf_le_left inf_le_right
  have hg := a.holo _ u.val
  have hf : ContDiffAt ℂ 2 (ev p σ _ u.val ∘ a.e.symm) (a.e y) :=
    (SCV.analyticAt_of_differentiableOn (hg.mono fun v hv => ⟨hv.1, hv.2⟩) (ho.mem_nhds hm)).contDiffAt
  have h0 : (ev p σ _ u.val ∘ a.e.symm) (a.e y) ≠ 0 := ev_ne_zero hm.2 u.isUnit
  have hC : ContDiffAt ℝ 2 (fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v)) (a.e y) :=
    ((VMetric.det Hm).cInf σ).contDiffAt a hy' hc'
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(ev p σ _ u.val ∘ a.e.symm) v‖ ^ 2)) (a.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have key : leviForm (fun v => ((VMetric.det Hm).φ σ).φ b (a.e.symm v)) (a.e y) =
      leviForm (fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v)) (a.e y) := by
    rw [leviForm_congr (u' := fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v) +
        -Real.log (‖(ev p σ _ u.val ∘ a.e.symm) v‖ ^ 2)), leviForm_add hC hlog.neg,
      leviForm_neg, leviForm_log_normSq_eq_zero hf h0, neg_zero, add_zero]
    filter_upwards [ho.mem_nhds hm] with v hv
    rw [((VMetric.det Hm).φ σ).trans c b _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, sub_eq_add_neg]
    rfl
  have eL : c1F hX σ (VMetric.det Hm) ⟨(a, y), hy⟩ =
      ofValues (HermFrame.ddc (fun v => ((VMetric.det Hm).φ σ).φ b (a.e.symm v)) (a.e y)) := rfl
  rw [eL]
  unfold HermFrame.ddc
  rw [key]
  have hM : MContDiffAt 2 (fun w => (m.met σ).G c (a.e.symm w)) (a.e y) :=
    (((Hm σ) c y hc).mContDiffAt a hy').of_le (WithTop.coe_le_coe.2 le_top)
  have hH : ∀ᶠ w in 𝓝 (a.e y), ((m.met σ).G c (a.e.symm w)).IsHermitian := by
    filter_upwards [ho.mem_nhds hm] with v hv
    exact ((m.met σ).posDef c _ (mem_ptsIn_inf.1 hv.2).1).1
  have hU : IsUnit ((m.met σ).G c (a.e.symm (a.e y))).det := by
    rw [a.e.left_inv hy']
    exact ((m.met σ).posDef c y hc).det_pos.ne'.isUnit
  have e2 : (fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v)) =
      fun v => -Real.log ((m.met σ).G c (a.e.symm v)).det.re := rfl
  change _ = ofValues (chernOne (fun w => (m.met σ).G c (a.e.symm w)) (a.e y))
  congr 1
  funext ξ η
  rw [chernOne_eq_neg_ddc_log_det hM hH hU, e2, leviForm_neg, ddc]
  simp

end GlobalTheory.LineForm.DdcLine

namespace GlobalTheory.LineForm.DdcLine

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
variable (hX : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2)

theorem restrict_G_sub (a : VBExt.AdaptedChart (lineSC fl) 1 1) (y : CxPts p σ) :
    ((h.restrict (fl.isSubbundle 1) (fl.isVB 1)).met σ).G a.sub y = subGram ((h.met σ).gram a.frame y) := by
  ext i j
  simp only [VMetric.restrict, Met.restrict, Met.gram, subGram, Matrix.toBlocks₁₁, Matrix.of_apply,
    VBExt.AdaptedChart.frame, VBExt.AdaptedChart.sub, Sum.elim_inl]

theorem quot_G_line (a : VBExt.AdaptedChart (lineSC fl) 1 1) {y : CxPts p σ} (hy : y ∈ ptsIn p σ a.U) :
    ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1)).met σ).G
      a.quot y = quotGram ((h.met σ).gram a.frame y) :=
  Met.quot_G (S := lineSC fl) (r := 1) (s := 1) (h.met σ) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) a hy

theorem isometric_quot_line :
    (VMetric.det (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1) H)).Isometric
      (VMetric.det (VMetric.IsCInf.quot (S := .mk _ _ (line_lineQuot fl)) (r := 1) (s := 1) (shortExact_lineQuot fl)
        (fl.isVB 1) (fl.isVB_gr 1) H)) :=
  (isometric_detQuot_and_bcInt_eq_of_iso k X p (lineSC fl) (.mk _ _ (line_lineQuot fl)) 1 1 h h H H
    (lineSC_shortExact fl) (shortExact_lineQuot fl) (fl.isVB 1) (fl.isVB_cokernel 1) (fl.isVB 1) (fl.isVB_gr 1)
    (Iso.refl _) (Iso.refl _) (by simp) (fun σ V s t y hy => by simp)).1

theorem c1F_grLB_zero_eq_chernOne_subGram (x : (hX.atlas σ).Pt) : c1F hX σ (VMetric.grLB fl 0 H) x =
    ofValues (chernOne (fun w => subGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) x.crd) := by
  have e₁ : c1F hX σ (VMetric.grLB fl 0 H) x =
      c1F hX σ (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))) x := by
    rw [c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_zero H fl)]
  have e₂ : c1F hX σ (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))) x =
      ofValues (chernOne (fun w => ((h.restrict (fl.isSubbundle 1) (fl.isVB 1)).met σ).G (frameAt fl x.pt).sub
        (x.ch.symm w)) x.crd) :=
    c1F_det_metric_eq_chernOne hX σ _ x (frameAt fl x.pt).sub (mem_frameAt fl x.pt)
  have e₃ : (fun w => ((h.restrict (fl.isSubbundle 1) (fl.isVB 1)).met σ).G (frameAt fl x.pt).sub (x.ch.symm w)) =
      fun w => subGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w)) :=
    funext fun w => restrict_G_sub σ h fl _ _
  rw [e₁, e₂, e₃]

theorem c1F_grLB_one_eq_chernOne_quotGram (x : (hX.atlas σ).Pt) : c1F hX σ (VMetric.grLB fl 1 H) x =
    ofValues (chernOne (fun w => quotGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) x.crd) := by
  have e₁ : c1F hX σ (VMetric.grLB fl 1 H) x = c1F hX σ (VMetric.det (VMetric.IsCInf.quot (S := lineSC fl) (r := 1)
      (s := 1) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) H)) x := by
    rw [c1F_eq_of_isometric k X p D hX σ _ _ (isometric_quot_line h H fl),
      c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_one H fl)]
  have e₂ : c1F hX σ (VMetric.det (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) (lineSC_shortExact fl)
      (fl.isVB 1) (fl.isVB_cokernel 1) H)) x =
      ofValues (chernOne (fun w => ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
        (fl.isVB_cokernel 1)).met σ).G (frameAt fl x.pt).quot (x.ch.symm w)) x.crd) :=
    c1F_det_metric_eq_chernOne hX σ (m := VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1)) (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1) H) x (frameAt fl x.pt).quot (mem_frameAt fl x.pt)
  have he : (fun w => ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1)).met σ).G (frameAt fl x.pt).quot (x.ch.symm w)) =ᶠ[𝓝 x.crd]
      (fun w => quotGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) := by
    filter_upwards [(isOpen_chartSet (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1).mem_nhds (crd_mem hX σ h H fl x)]
      with v hv
    have hv2 : x.ch.symm v ∈ ptsIn p σ (frameAt fl x.pt).U := hv.2
    exact quot_G_line σ h fl (frameAt fl x.pt) hv2
  have e₃ : chernOne (fun w => ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1)).met σ).G (frameAt fl x.pt).quot (x.ch.symm w)) x.crd =
      chernOne (fun w => quotGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) x.crd := by
    funext ξ η
    simp only [chernOne]
    rw [curv_congr he]
  rw [e₁, e₂, e₃]

theorem ofValuesTwo_sub {n : ℕ} (Ψ Φ : V n → V n → V n → V n → ℂ) :
    ofValuesTwo (fun a b c d => Ψ a b c d - Φ a b c d) = ofValuesTwo Ψ - ofValuesTwo Φ := by
  simp only [ofValuesTwo, sub_smul, Finset.sum_sub_distrib, smul_sub]

theorem ddc_omF : (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
    fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H)) := by
  funext x
  have hmem := crd_mem hX σ h H fl x
  have hpos := isPosFrame_midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1
  rw [GlobalTheory.T.ddc_eq_of_local_eq _ _ x _ (loc_omF hX σ h H fl x), GlobalTheory.T.ddc_ofValues_eq _ _ (fun a b =>
    ((GlobalTheory.T.contDiffOn_extTrace_of_isPosFrame hpos _ _).contDiffAt (hpos.1.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top))]
  have hc := (((GlobalTheory.SubQuotCurv.subQuotCurvature _ (Fin 1) (Fin 1) _ _).2 hpos).2.2.2 (by simp) (by simp) _ hmem).2.2.2
  have hd : ddcForm (extTrace (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1)) x.crd = fun ξ₁ η₁ ξ₂ η₂ =>
      chernTwo (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1) x.crd ξ₁ η₁ ξ₂ η₂ -
        wedge (chernOne (GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramS (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1)) x.crd)
          (chernOne (GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramQ (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1)) x.crd) ξ₁ η₁ ξ₂ η₂ := by
    funext ξ₁ η₁ ξ₂ η₂; exact hc ξ₁ η₁ ξ₂ η₂
  rw [hd, ofValuesTwo_sub, ← GlobalTheory.T.chernAt_two_eq_ofValuesTwo_chernTwo, ← GlobalTheory.T.ofValues_mul_ofValues']
  simp only [fld, Pi.sub_apply, Pi.mul_apply, c1F_grLB_zero_eq_chernOne_subGram hX σ h H fl x, c1F_grLB_one_eq_chernOne_quotGram hX σ h H fl x]
  rfl

end GlobalTheory.LineForm.DdcLine

theorem GlobalTheory.LineForm.ddc_omF_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
      fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H)) :=
  fun _ _ _ _ _ _ hX σ _ h H fl => GlobalTheory.LineForm.DdcLine.ddc_omF hX σ h H fl
