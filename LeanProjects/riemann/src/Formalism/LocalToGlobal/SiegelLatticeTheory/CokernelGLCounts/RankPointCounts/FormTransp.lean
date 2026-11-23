import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameNormal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPinG
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

noncomputable section

open MeasureTheory Set Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.Vanish
open scoped ENNReal

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RelCharC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), t.relevant →
    ∀ r ∈ Rset t, X.psiInfU u r = X.psiInfU u' (t.pt.1⁻¹ * r * t.pt.1)

namespace FormTranspose

variable {D : D7} (X : HidaSetting D)

theorem ninf_mul (u : D.what₂.Word) {a b : X.B.I.Ginf} (ha : a ∈ X.NinfU u) (hb : b ∈ X.NinfU u) : a * b ∈ X.NinfU u := (NinfSub X.eR (X.zR u)).mul_mem ha hb

theorem ninf_inv (u : D.what₂.Word) {a : X.B.I.Ginf} (ha : a ∈ X.NinfU u) : a⁻¹ ∈ X.NinfU u := (NinfSub X.eR (X.zR u)).inv_mem ha

theorem sinf_conj (u : D.what₂.Word) {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) {n : X.B.I.Ginf} (hn : n ∈ X.NinfU u) :
    a * n * a⁻¹ ∈ X.NinfU u := by
  obtain ⟨h, hh, m, hm, rfl⟩ := Sinf.levi X u ha
  have e : h * m * n * (h * m)⁻¹ = h * (m * n * m⁻¹) * h⁻¹ := by group
  rw [e]
  exact Sinf.conj_ninf X u hh (ninf_mul X u (ninf_mul X u hm hn) (ninf_inv X u hm))

theorem sinf_conj_iff (u : D.what₂.Word) {a : X.B.I.Ginf} (ha : a ∈ X.SinfU u) (n : X.B.I.Ginf) :
    a * n * a⁻¹ ∈ X.NinfU u ↔ n ∈ X.NinfU u := by
  constructor
  · intro h
    have ha' : a⁻¹ ∈ X.SinfU u := (SinfSub X.B.I X.eR (X.zR u)).inv_mem ha
    have h2 := sinf_conj X u ha' h
    simpa [mul_assoc] using h2
  · exact fun hn => sinf_conj X u ha hn

end FormTranspose

open FormTranspose

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (κ : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem normRep_atPt (t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) (w' : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1))
    (F' : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hN : Formalism.L2.SG.PairVal.NormRep t w' F' L U) (hG : t.G ≠ 0) : t.atPt w' := by
  obtain ⟨⟨h, hmk⟩, -, hL, hU, hZ⟩ := hN
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam ((Y.rowsOK u).1 t.lam t.mem)).1
  have hG' : Formalism.MainNotions.S.Lat.Gval (lf D (X.Fu u)) F' ≠ 0 := by
    intro h0
    apply hG
    change TermDef.Gt t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') t.cls = 0
    rw [← hmk]
    exact (TermDef.Gt_mk hGF ⟨F', h⟩).trans h0
  exact ⟨F', ⟨h, hmk⟩, hG', ⟨L, U, hL, hU, hZ⟩⟩

theorem formTransp_term (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq) (hV : Formalism.L2.SG.VolPin.VolPinC) (hRC : RelCharC)
    (hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u))
    (hCPU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hNRat : ∀ (t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) w' F' L U,
      Formalism.L2.SG.PairVal.NormRep t w' F' L U → t.G ≠ 0 → t.atPt w')
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hrel : t.relevant) (hgen : t.toTerm.generic)
    (hG : t.G ≠ 0) (hat : t.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t.toTerm))
    (hreal : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ)
    (g : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (g' : X.B.I.Ginf) (hg' : g' ∈ X.SinfU u')
    (hdec : t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) * g'⁻¹) :
    haveI := FiniteDimensional.complete ℂ (X.Vpi u)
    OOt t = ((Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm : ℝ) : ℂ) •
      OO ((νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm))).map (fun x => g * x))
        Set.univ (X.Wu u) (X.Wu u') t.pt.1 := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  set w := Formalism.L2.SG.PairVal.ptOf t.toTerm with hw
  set γw := Formalism.L2.SG.RealObj.gamW X u u' w with hγw
  have hγwP : Formalism.L2.SG.RealObj.IsPtRep X u u' w γw := by
    simp only [hγw, Formalism.L2.SG.RealObj.gamW, dif_pos hreal]; exact hreal.choose_spec
  obtain ⟨μw, hμwH, hμwQ, hμwS⟩ := hP.2 w hreal

  set cj : X.B.I.Ginf → X.B.I.Ginf := fun y => g * y * g⁻¹ with hcj
  have hcjm : Measurable cj := (measurable_const_mul g).mul_const g⁻¹
  set μR := μw.map cj with hμR
  set ν := (νq γw).map (fun x => g * x) with hν

  have hRset : ∀ z, cj z ∈ Rset t ↔ z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := by
    intro z
    have e2 : t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 = g' * (γw⁻¹ * z * γw) * g'⁻¹ := by
      rw [show t.pt.1 = g * γw * g'⁻¹ from hdec]; group
    show (g * z * g⁻¹ ∈ X.NinfU u ∧ t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 ∈ X.NinfU u') ↔
      (z ∈ X.NinfU u ∧ γw⁻¹ * z * γw ∈ X.NinfU u')
    rw [e2, sinf_conj_iff X u hg, sinf_conj_iff X u' hg']
  have hHaar : IsHaarOnSet X.B.I (Rset t) μR := by
    obtain ⟨h1, h2, h3, h4⟩ := hμwH
    have hcje : MeasurableEquiv X.B.I.Ginf X.B.I.Ginf :=
      (MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : SigmaFinite μw := h1
      exact ((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)).sigmaFinite_map
    · intro h0
      apply h2
      have := congrArg (fun m : Measure X.B.I.Ginf => m univ) h0
      simp only [hμR, Measure.map_apply hcjm MeasurableSet.univ, preimage_univ, Measure.coe_zero,
        Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    · have hcje : ⇑((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)) = cj := rfl
      rw [hμR, ← hcje, MeasurableEquiv.map_apply]
      refine measure_mono_null (fun z hz => ?_) h3
      intro hzS; exact hz ((hRset z).2 hzS)
    · intro r hr
      set z := g⁻¹ * r * g with hz
      have hcz : cj z = r := by simp only [hcj, hz]; group
      have hzS : z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := (hRset z).1 (hcz ▸ hr)
      have hcomp : (fun y => r * y) ∘ cj = cj ∘ (fun y => z * y) := by
        funext y; simp only [Function.comp, hcj, hz]; group
      rw [hμR, Measure.map_map (measurable_const_mul r) hcjm, hcomp,
        ← Measure.map_map hcjm (measurable_const_mul z), h4 z hzS]

  have hmulm : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_mul
  have hQ' : IsQuotMeasS X.B.I μR ν := by
    intro f hf
    have hσ : SigmaFinite μw := hμwH.1
    have hσR : SigmaFinite μR := hHaar.1
    have hF : Measurable fun x => ∫⁻ s, f (s * x) ∂μR := (hf.comp hmulm).lintegral_prod_left'
    rw [hν, lintegral_map hF (measurable_const_mul g)]
    have e1 : ∀ x0, ∫⁻ s, f (s * (g * x0)) ∂μR = ∫⁻ z, (fun y => f (g * y)) (z * x0) ∂μw := by
      intro x0
      rw [hμR, lintegral_map (f := fun s => f (s * (g * x0))) (hf.comp (measurable_mul_const _)) hcjm]
      refine lintegral_congr fun z => ?_
      simp only [hcj]
      congr 1
      group
    simp only [e1]
    rw [← hμwQ (fun y => f (g * y)) (hf.comp (measurable_const_mul g))]
    exact (lintegral_mul_left_eq_self f g).symm

  have hFE : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := fundExistsC_holds D X Y u u' t
  have hFO : IsSFund X.B.I (ROinf t) (FundOf t) := by
    unfold FundOf; rw [dif_pos hFE]; exact hFE.choose_spec
  set Γ0 := ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin with hΓ0
  have hKu : ∀ r ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * r ∈ FundOf t := by
    intro r _
    obtain ⟨s0, hs0, hs0F⟩ := hFO.2.1 r
    refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
    have h2 : (s0 * s'⁻¹) * (s' * r) ∈ FundOf t := by simpa [mul_assoc] using hs0F
    have := hFO.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
    exact (mul_inv_eq_one.1 this).symm
  have hFA := formAllC_holds D X Y u u' t μR ν (FundOf t) (hRC D X Y u u' t hrel) hHaar hQ' hFO.1 hKu

  have hPin : Formalism.L2.SG.VolPin.IsPinnedR t w μR := ⟨γw, g, g', μw, hγwP, hg, hg', hdec, hμwH, hμwS, rfl⟩
  have hNRex := hNR t.toTerm w hat hrel hgen
  have hvR : Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm = (μR (FundOf t)).toReal := by
    unfold Formalism.L2.SG.PairVal.vRdef
    split_ifs with hc
    · have hx := hc.2.2.choose_spec
      have hw' : hc.2.2.choose.1 = w := hCPU t.toTerm _ _ (hNRat _ _ _ _ _ hx hG) hat
      have hx' := hx
      rw [hw'] at hx'
      rw [hw']
      exact (hV D X Y u u' t hrel hG w hat μR hPin (FundOf t) hFO.1 hKu _ _ _ hx').symm
    · exfalso
      obtain ⟨x, hx⟩ := hNRex
      exact hc ⟨hrel, hgen, ⟨(w, x.1, x.2.1, x.2.2), hx⟩⟩
  rw [hFA, hvR, Complex.coe_smul]

theorem formTransp_any (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq) (hRC : RelCharC)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hrel : t.relevant)
    (hreal : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ)
    (g : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (g' : X.B.I.Ginf) (hg' : g' ∈ X.SinfU u')
    (hdec : t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) * g'⁻¹) :
    haveI := FiniteDimensional.complete ℂ (X.Vpi u)
    ∃ c : ℝ, OOt t = c •
      OO ((νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm))).map (fun x => g * x))
        Set.univ (X.Wu u) (X.Wu u') t.pt.1 := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  set w := Formalism.L2.SG.PairVal.ptOf t.toTerm with hw
  set γw := Formalism.L2.SG.RealObj.gamW X u u' w with hγw
  have hγwP : Formalism.L2.SG.RealObj.IsPtRep X u u' w γw := by
    simp only [hγw, Formalism.L2.SG.RealObj.gamW, dif_pos hreal]; exact hreal.choose_spec
  obtain ⟨μw, hμwH, hμwQ, hμwS⟩ := hP.2 w hreal

  set cj : X.B.I.Ginf → X.B.I.Ginf := fun y => g * y * g⁻¹ with hcj
  have hcjm : Measurable cj := (measurable_const_mul g).mul_const g⁻¹
  set μR := μw.map cj with hμR
  set ν := (νq γw).map (fun x => g * x) with hν

  have hRset : ∀ z, cj z ∈ Rset t ↔ z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := by
    intro z
    have e2 : t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 = g' * (γw⁻¹ * z * γw) * g'⁻¹ := by
      rw [show t.pt.1 = g * γw * g'⁻¹ from hdec]; group
    show (g * z * g⁻¹ ∈ X.NinfU u ∧ t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 ∈ X.NinfU u') ↔
      (z ∈ X.NinfU u ∧ γw⁻¹ * z * γw ∈ X.NinfU u')
    rw [e2, sinf_conj_iff X u hg, sinf_conj_iff X u' hg']
  have hHaar : IsHaarOnSet X.B.I (Rset t) μR := by
    obtain ⟨h1, h2, h3, h4⟩ := hμwH
    have hcje : MeasurableEquiv X.B.I.Ginf X.B.I.Ginf :=
      (MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : SigmaFinite μw := h1
      exact ((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)).sigmaFinite_map
    · intro h0
      apply h2
      have := congrArg (fun m : Measure X.B.I.Ginf => m univ) h0
      simp only [hμR, Measure.map_apply hcjm MeasurableSet.univ, preimage_univ, Measure.coe_zero,
        Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    · have hcje : ⇑((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)) = cj := rfl
      rw [hμR, ← hcje, MeasurableEquiv.map_apply]
      refine measure_mono_null (fun z hz => ?_) h3
      intro hzS; exact hz ((hRset z).2 hzS)
    · intro r hr
      set z := g⁻¹ * r * g with hz
      have hcz : cj z = r := by simp only [hcj, hz]; group
      have hzS : z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := (hRset z).1 (hcz ▸ hr)
      have hcomp : (fun y => r * y) ∘ cj = cj ∘ (fun y => z * y) := by
        funext y; simp only [Function.comp, hcj, hz]; group
      rw [hμR, Measure.map_map (measurable_const_mul r) hcjm, hcomp,
        ← Measure.map_map hcjm (measurable_const_mul z), h4 z hzS]

  have hmulm : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_mul
  have hQ' : IsQuotMeasS X.B.I μR ν := by
    intro f hf
    have hσ : SigmaFinite μw := hμwH.1
    have hσR : SigmaFinite μR := hHaar.1
    have hF : Measurable fun x => ∫⁻ s, f (s * x) ∂μR := (hf.comp hmulm).lintegral_prod_left'
    rw [hν, lintegral_map hF (measurable_const_mul g)]
    have e1 : ∀ x0, ∫⁻ s, f (s * (g * x0)) ∂μR = ∫⁻ z, (fun y => f (g * y)) (z * x0) ∂μw := by
      intro x0
      rw [hμR, lintegral_map (f := fun s => f (s * (g * x0))) (hf.comp (measurable_mul_const _)) hcjm]
      refine lintegral_congr fun z => ?_
      simp only [hcj]
      congr 1
      group
    simp only [e1]
    rw [← hμwQ (fun y => f (g * y)) (hf.comp (measurable_const_mul g))]
    exact (lintegral_mul_left_eq_self f g).symm

  have hFE : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := fundExistsC_holds D X Y u u' t
  have hFO : IsSFund X.B.I (ROinf t) (FundOf t) := by
    unfold FundOf; rw [dif_pos hFE]; exact hFE.choose_spec
  set Γ0 := ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin with hΓ0
  have hKu : ∀ r ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * r ∈ FundOf t := by
    intro r _
    obtain ⟨s0, hs0, hs0F⟩ := hFO.2.1 r
    refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
    have h2 : (s0 * s'⁻¹) * (s' * r) ∈ FundOf t := by simpa [mul_assoc] using hs0F
    have := hFO.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
    exact (mul_inv_eq_one.1 this).symm
  have hFA := formAllC_holds D X Y u u' t μR ν (FundOf t) (hRC D X Y u u' t hrel) hHaar hQ' hFO.1 hKu
  exact ⟨_, hFA⟩

theorem formTranspC_of (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq) (hV : Formalism.L2.SG.VolPin.VolPinC) (hRC : RelCharC)
    (hLD : RowForm.LiftDecompC X Y u u' κ) (hAt : RowForm.LiftAtSomeC X Y u u' κ)
    (hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u))
    (hCPU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hNRat : ∀ (t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) w' F' L U,
      Formalism.L2.SG.PairVal.NormRep t w' F' L U → t.G ≠ 0 → t.atPt w') :
    RowForm.FormTranspC X Y u u' (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) νq κ := by
  intro R ρ s hrel g hg g' hg' hdec
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) := by
    obtain ⟨w0, hw0⟩ := hAt R ρ s hrel
    exact Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hG : s.1.G ≠ 0 := by
    have h1 := s.2.1
    intro h0
    apply h1
    show Gt s.1 = 0
    unfold Gt; rw [if_pos h0]
  exact formTransp_term X Y u u' νq hP hV hRC hNR hCPU hNRat s.1 hrel s.2.2.1 hG hat (hLD R ρ s hrel).1 g hg g' hg' hdec

theorem formTranspC_of' (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq) (hV : Formalism.L2.SG.VolPin.VolPinC) (hRC : RelCharC)
    (hLD : RowForm.LiftDecompC X Y u u' κ) (hAt : RowForm.LiftAtSomeC X Y u u' κ)
    (hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u))
    (hCPU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u)) :
    RowForm.FormTranspC X Y u u' (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) νq κ := formTranspC_of X Y u u' νq κ hP hV hRC hLD hAt hNR hCPU
  (fun t w' F' L U hN hG => normRep_atPt X Y u u' t w' F' L U hN hG)

theorem formTransp_termG (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq) (hV : Formalism.L2.SG.VolPin.VolPinGC)
    (hPH : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) (hRC : RelCharC)
    (hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u))
    (hCPU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hNRat : ∀ (t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) w' F' L U,
      Formalism.L2.SG.PairVal.NormRep t w' F' L U → t.G ≠ 0 → t.atPt w')
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hrel : t.relevant) (hgen : t.toTerm.generic)
    (hG : t.G ≠ 0) (hat : t.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t.toTerm))
    (hreal : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ)
    (g : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (g' : X.B.I.Ginf) (hg' : g' ∈ X.SinfU u')
    (hdec : t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) * g'⁻¹) :
    haveI := FiniteDimensional.complete ℂ (X.Vpi u)
    OOt t = ((Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm : ℝ) : ℂ) •
      OO ((νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm))).map (fun x => g * x))
        Set.univ (X.Wu u) (X.Wu u') t.pt.1 := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  set w := Formalism.L2.SG.PairVal.ptOf t.toTerm with hw
  set γw := Formalism.L2.SG.RealObj.gamW X u u' w with hγw
  have hγwP : Formalism.L2.SG.RealObj.IsPtRep X u u' w γw := by
    simp only [hγw, Formalism.L2.SG.RealObj.gamW, dif_pos hreal]; exact hreal.choose_spec
  obtain ⟨μw, hμwH, hμwQ, hμwS⟩ := hP.2 w hreal

  set cj : X.B.I.Ginf → X.B.I.Ginf := fun y => g * y * g⁻¹ with hcj
  have hcjm : Measurable cj := (measurable_const_mul g).mul_const g⁻¹
  set μR := μw.map cj with hμR
  set ν := (νq γw).map (fun x => g * x) with hν

  have hRset : ∀ z, cj z ∈ Rset t ↔ z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := by
    intro z
    have e2 : t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 = g' * (γw⁻¹ * z * γw) * g'⁻¹ := by
      rw [show t.pt.1 = g * γw * g'⁻¹ from hdec]; group
    show (g * z * g⁻¹ ∈ X.NinfU u ∧ t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 ∈ X.NinfU u') ↔
      (z ∈ X.NinfU u ∧ γw⁻¹ * z * γw ∈ X.NinfU u')
    rw [e2, sinf_conj_iff X u hg, sinf_conj_iff X u' hg']
  have hHaar : IsHaarOnSet X.B.I (Rset t) μR := by
    obtain ⟨h1, h2, h3, h4⟩ := hμwH
    have hcje : MeasurableEquiv X.B.I.Ginf X.B.I.Ginf :=
      (MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : SigmaFinite μw := h1
      exact ((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)).sigmaFinite_map
    · intro h0
      apply h2
      have := congrArg (fun m : Measure X.B.I.Ginf => m univ) h0
      simp only [hμR, Measure.map_apply hcjm MeasurableSet.univ, preimage_univ, Measure.coe_zero,
        Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    · have hcje : ⇑((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)) = cj := rfl
      rw [hμR, ← hcje, MeasurableEquiv.map_apply]
      refine measure_mono_null (fun z hz => ?_) h3
      intro hzS; exact hz ((hRset z).2 hzS)
    · intro r hr
      set z := g⁻¹ * r * g with hz
      have hcz : cj z = r := by simp only [hcj, hz]; group
      have hzS : z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := (hRset z).1 (hcz ▸ hr)
      have hcomp : (fun y => r * y) ∘ cj = cj ∘ (fun y => z * y) := by
        funext y; simp only [Function.comp, hcj, hz]; group
      rw [hμR, Measure.map_map (measurable_const_mul r) hcjm, hcomp,
        ← Measure.map_map hcjm (measurable_const_mul z), h4 z hzS]

  have hmulm : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_mul
  have hQ' : IsQuotMeasS X.B.I μR ν := by
    intro f hf
    have hσ : SigmaFinite μw := hμwH.1
    have hσR : SigmaFinite μR := hHaar.1
    have hF : Measurable fun x => ∫⁻ s, f (s * x) ∂μR := (hf.comp hmulm).lintegral_prod_left'
    rw [hν, lintegral_map hF (measurable_const_mul g)]
    have e1 : ∀ x0, ∫⁻ s, f (s * (g * x0)) ∂μR = ∫⁻ z, (fun y => f (g * y)) (z * x0) ∂μw := by
      intro x0
      rw [hμR, lintegral_map (f := fun s => f (s * (g * x0))) (hf.comp (measurable_mul_const _)) hcjm]
      refine lintegral_congr fun z => ?_
      simp only [hcj]
      congr 1
      group
    simp only [e1]
    rw [← hμwQ (fun y => f (g * y)) (hf.comp (measurable_const_mul g))]
    exact (lintegral_mul_left_eq_self f g).symm

  have hFE : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := fundExistsC_holds D X Y u u' t
  have hFO : IsSFund X.B.I (ROinf t) (FundOf t) := by
    unfold FundOf; rw [dif_pos hFE]; exact hFE.choose_spec
  set Γ0 := ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin with hΓ0
  have hKu : ∀ r ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * r ∈ FundOf t := by
    intro r _
    obtain ⟨s0, hs0, hs0F⟩ := hFO.2.1 r
    refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
    have h2 : (s0 * s'⁻¹) * (s' * r) ∈ FundOf t := by simpa [mul_assoc] using hs0F
    have := hFO.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
    exact (mul_inv_eq_one.1 this).symm
  have hFA := formAllC_holds D X Y u u' t μR ν (FundOf t) (hRC D X Y u u' t hrel) hHaar hQ' hFO.1 hKu

  have hPin : Formalism.L2.SG.VolPin.IsPinnedR t w μR := ⟨γw, g, g', μw, hγwP, hg, hg', hdec, hμwH, hμwS, rfl⟩
  have hNRex := hNR t.toTerm w hat hrel hgen
  have hvR : Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm = (μR (FundOf t)).toReal := by
    unfold Formalism.L2.SG.PairVal.vRdef
    split_ifs with hc
    · have hx := hc.2.2.choose_spec
      have hw' : hc.2.2.choose.1 = w := hCPU t.toTerm _ _ (hNRat _ _ _ _ _ hx hG) hat
      have hx' := hx
      rw [hw'] at hx'
      rw [hw']
      exact (hV D X Y u u' hPH t hrel hgen hG w hat μR hPin (FundOf t) hFO.1 hKu _ _ _ hx').symm
    · exfalso
      obtain ⟨x, hx⟩ := hNRex
      exact hc ⟨hrel, hgen, ⟨(w, x.1, x.2.1, x.2.2), hx⟩⟩
  rw [hFA, hvR, Complex.coe_smul]

theorem formTranspC_ofG (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq) (hV : Formalism.L2.SG.VolPin.VolPinGC)
    (hPH : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) (hRC : RelCharC)
    (hLD : RowForm.LiftDecompC X Y u u' κ) (hAt : RowForm.LiftAtSomeC X Y u u' κ)
    (hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u))
    (hCPU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u)) :
    RowForm.FormTranspC X Y u u' (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) νq κ := by
  intro R ρ s hrel g hg g' hg' hdec
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) := by
    obtain ⟨w0, hw0⟩ := hAt R ρ s hrel
    exact Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hG : s.1.G ≠ 0 := by
    have h1 := s.2.1
    intro h0
    apply h1
    show Gt s.1 = 0
    unfold Gt; rw [if_pos h0]
  exact formTransp_termG X Y u u' νq hP hV hPH hRC hNR hCPU
    (fun t w' F' L U hN hG => normRep_atPt X Y u u' t w' F' L U hN hG) s.1 hrel s.2.2.1 hG hat (hLD R ρ s hrel).1
    g hg g' hg' hdec

theorem formula_transport_term (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq) (hV : Formalism.L2.SG.VolPin.VolumeOddGeneric)
    (hg3 : ∀ i, 3 ≤ D.host.g i) (hPH : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) (hRC : RelCharC)
    (hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u))
    (hCPU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hNRat : ∀ (t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) w' F' L U,
      Formalism.L2.SG.PairVal.NormRep t w' F' L U → t.G ≠ 0 → t.atPt w')
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hrel : t.relevant) (hgen : t.toTerm.generic)
    (hG : t.G ≠ 0) (hat : t.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t.toTerm))
    (hreal : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ)
    (g : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (g' : X.B.I.Ginf) (hg' : g' ∈ X.SinfU u')
    (hdec : t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) * g'⁻¹) :
    haveI := FiniteDimensional.complete ℂ (X.Vpi u)
    OOt t = ((Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm : ℝ) : ℂ) •
      OO ((νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm))).map (fun x => g * x))
        Set.univ (X.Wu u) (X.Wu u') t.pt.1 := by
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  set w := Formalism.L2.SG.PairVal.ptOf t.toTerm with hw
  set γw := Formalism.L2.SG.RealObj.gamW X u u' w with hγw
  have hγwP : Formalism.L2.SG.RealObj.IsPtRep X u u' w γw := by
    simp only [hγw, Formalism.L2.SG.RealObj.gamW, dif_pos hreal]; exact hreal.choose_spec
  obtain ⟨μw, hμwH, hμwQ, hμwS⟩ := hP.2 w hreal

  set cj : X.B.I.Ginf → X.B.I.Ginf := fun y => g * y * g⁻¹ with hcj
  have hcjm : Measurable cj := (measurable_const_mul g).mul_const g⁻¹
  set μR := μw.map cj with hμR
  set ν := (νq γw).map (fun x => g * x) with hν

  have hRset : ∀ z, cj z ∈ Rset t ↔ z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := by
    intro z
    have e2 : t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 = g' * (γw⁻¹ * z * γw) * g'⁻¹ := by
      rw [show t.pt.1 = g * γw * g'⁻¹ from hdec]; group
    show (g * z * g⁻¹ ∈ X.NinfU u ∧ t.pt.1⁻¹ * (g * z * g⁻¹) * t.pt.1 ∈ X.NinfU u') ↔
      (z ∈ X.NinfU u ∧ γw⁻¹ * z * γw ∈ X.NinfU u')
    rw [e2, sinf_conj_iff X u hg, sinf_conj_iff X u' hg']
  have hHaar : IsHaarOnSet X.B.I (Rset t) μR := by
    obtain ⟨h1, h2, h3, h4⟩ := hμwH
    have hcje : MeasurableEquiv X.B.I.Ginf X.B.I.Ginf :=
      (MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : SigmaFinite μw := h1
      exact ((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)).sigmaFinite_map
    · intro h0
      apply h2
      have := congrArg (fun m : Measure X.B.I.Ginf => m univ) h0
      simp only [hμR, Measure.map_apply hcjm MeasurableSet.univ, preimage_univ, Measure.coe_zero,
        Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    · have hcje : ⇑((MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)) = cj := rfl
      rw [hμR, ← hcje, MeasurableEquiv.map_apply]
      refine measure_mono_null (fun z hz => ?_) h3
      intro hzS; exact hz ((hRset z).2 hzS)
    · intro r hr
      set z := g⁻¹ * r * g with hz
      have hcz : cj z = r := by simp only [hcj, hz]; group
      have hzS : z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw := (hRset z).1 (hcz ▸ hr)
      have hcomp : (fun y => r * y) ∘ cj = cj ∘ (fun y => z * y) := by
        funext y; simp only [Function.comp, hcj, hz]; group
      rw [hμR, Measure.map_map (measurable_const_mul r) hcjm, hcomp,
        ← Measure.map_map hcjm (measurable_const_mul z), h4 z hzS]

  have hmulm : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_mul
  have hQ' : IsQuotMeasS X.B.I μR ν := by
    intro f hf
    have hσ : SigmaFinite μw := hμwH.1
    have hσR : SigmaFinite μR := hHaar.1
    have hF : Measurable fun x => ∫⁻ s, f (s * x) ∂μR := (hf.comp hmulm).lintegral_prod_left'
    rw [hν, lintegral_map hF (measurable_const_mul g)]
    have e1 : ∀ x0, ∫⁻ s, f (s * (g * x0)) ∂μR = ∫⁻ z, (fun y => f (g * y)) (z * x0) ∂μw := by
      intro x0
      rw [hμR, lintegral_map (f := fun s => f (s * (g * x0))) (hf.comp (measurable_mul_const _)) hcjm]
      refine lintegral_congr fun z => ?_
      simp only [hcj]
      congr 1
      group
    simp only [e1]
    rw [← hμwQ (fun y => f (g * y)) (hf.comp (measurable_const_mul g))]
    exact (lintegral_mul_left_eq_self f g).symm

  have hFE : ∃ Ω, IsSFund X.B.I (ROinf t) Ω := fundExistsC_holds D X Y u u' t
  have hFO : IsSFund X.B.I (ROinf t) (FundOf t) := by
    unfold FundOf; rw [dif_pos hFE]; exact hFE.choose_spec
  set Γ0 := ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin with hΓ0
  have hKu : ∀ r ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * r ∈ FundOf t := by
    intro r _
    obtain ⟨s0, hs0, hs0F⟩ := hFO.2.1 r
    refine ⟨s0, ⟨hs0, hs0F⟩, fun s' ⟨hs', hs'F⟩ => ?_⟩
    have h2 : (s0 * s'⁻¹) * (s' * r) ∈ FundOf t := by simpa [mul_assoc] using hs0F
    have := hFO.2.2 _ hs'F _ (Γ0.mul_mem hs0 (Γ0.inv_mem hs')) h2
    exact (mul_inv_eq_one.1 this).symm
  have hFA := formAllC_holds D X Y u u' t μR ν (FundOf t) (hRC D X Y u u' t hrel) hHaar hQ' hFO.1 hKu

  have hPin : Formalism.L2.SG.VolPin.IsPinnedR t w μR := ⟨γw, g, g', μw, hγwP, hg, hg', hdec, hμwH, hμwS, rfl⟩
  have hNRex := hNR t.toTerm w hat hrel hgen
  have hvR : Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm = (μR (FundOf t)).toReal := by
    unfold Formalism.L2.SG.PairVal.vRdef
    split_ifs with hc
    · have hx := hc.2.2.choose_spec
      have hw' : hc.2.2.choose.1 = w := hCPU t.toTerm _ _ (hNRat _ _ _ _ _ hx hG) hat
      have hx' := hx
      rw [hw'] at hx'
      rw [hw']
      exact (hV D X Y u u' hg3 hPH t hrel hgen hG w hat μR hPin (FundOf t) hFO.1 hKu _ _ _ hx').symm
    · exfalso
      obtain ⟨x, hx⟩ := hNRex
      exact hc ⟨hrel, hgen, ⟨(w, x.1, x.2.1, x.2.2), hx⟩⟩
  rw [hFA, hvR, Complex.coe_smul]

theorem formula_transport_of_condition (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq) (hV : Formalism.L2.SG.VolPin.VolumeOddGeneric)
    (hg3 : ∀ i, 3 ≤ D.host.g i) (hPH : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) (hRC : RelCharC)
    (hLD : RowForm.LiftDecompC X Y u u' κ) (hAt : RowForm.LiftAtSomeC X Y u u' κ)
    (hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u))
    (hCPU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u)) :
    RowForm.FormTranspC X Y u u' (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) νq κ := by
  intro R ρ s hrel g hg g' hg' hdec
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) := by
    obtain ⟨w0, hw0⟩ := hAt R ρ s hrel
    exact Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hG : s.1.G ≠ 0 := by
    have h1 := s.2.1
    intro h0
    apply h1
    show Gt s.1 = 0
    unfold Gt; rw [if_pos h0]
  exact formula_transport_term X Y u u' νq hP hV hg3 hPH hRC hNR hCPU
    (fun t w' F' L U hN hG => normRep_atPt X Y u u' t w' F' L U hN hG) s.1 hrel s.2.2.1 hG hat (hLD R ρ s hrel).1
    g hg g' hg' hdec

end Formalism.L2.SG.Pf
