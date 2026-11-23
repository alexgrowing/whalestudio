import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowFormAllOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsSumCPf

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem poincareConstant_pos {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word) :
    0 < Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X X u (Y.FN u) := by
  have hv := Formalism.L2.SG.Closed.VolPosC_holds D X Y u (Formalism.L2.SG.Closed.level_subgroup_properties X)
  haveI : Nontrivial (X.Vpi u) := Formalism.L2.SG.Pf.ColDictPf.vpi_nontrivial X u
  have hr : (0 : ℝ) < (Module.finrank ℂ (X.Vpi u) : ℝ) := by exact_mod_cast Module.finrank_pos
  rw [Formalism.L2.SG.Full.Full.poincare_constant_eq]
  exact div_pos (mul_pos hv.1 hv.2) hr

theorem ampValLowerC_vR {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hSt : Formalism.MainNotions.S.Cnt.Stand D u u') (hi : ∀ v, i0 v = i0' v) (hNuP : Formalism.L2.SG.RealObj.NuQPin X u u' νq)
    (hVP : Formalism.L2.SG.VolPin.VolPinGC) :
    Formalism.L2.SG.Pf.RowForm.ClassAbs.AmpValLowerC X Y u u'
      (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) i0 i0' νq := by
  have hPH : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') := Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
  have hi' : i0' = i0 := funext fun v => (hi v).symm
  subst hi'
  let κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ := fun _ => 0
  have hAtS : ∀ t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w :=
    fun t hG hr => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' t hG hr
  have hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.cell_point_unique_of_term_fun (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  have hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.normRepExists_of (Formalism.L2.SG.Pf.NormRepX.norm_representative_holds D u u' hPH)
      (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  have hLD : Formalism.L2.SG.Pf.RowForm.LiftDecompC X Y u u' κ :=
    Formalism.L2.SG.Pf.RowForm.liftDecompC_of_real (κ := κ) (h := Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of (hAt := hAtS))
  have hFT := Formalism.L2.SG.Pf.formTranspC_ofG (κ := κ) (hP := hNuP) (hV := hVP) (hPH := hPH)
    (hRC := Formalism.L2.SG.Pf.RelChar.relCharC_holds) (hLD := hLD) (hAt := Formalism.L2.SG.Pf.LiftedPhaseAgreement.liftAtSomeC_holds X Y u u' κ)
    (hNR := hNR) (hCPU := hCU)
  have hDF : Formalism.L2.SG.Pf.RowForm.DFrameAtS X u u' i0' i0' 1 := Formalism.L2.SG.Pf.Carrier.dual_frame_at_places X u u' 1 i0'
  have hNF := Formalism.L2.SG.Pf.RowForm.normalFormC_all (hAtS := hAtS) (hTP := fun t w h => Formalism.L2.SG.WConst.atPt_totPos t w h)
    (hCU := hCU) (hDF := hDF) (hPT := Formalism.L2.SG.Pf.LiftedPhaseAgreement.phaseTieC_holds (κ := κ) (hP := hPH)) (hFT := hFT)
  refine Formalism.L2.SG.Pf.ampValLowerC_of X Y u u' _ i0' i0' νq κ hNF
    (fun t w h => Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' _ _ t w h) ?_
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := by
    unfold Formalism.L2.SG.HidaSetting.HidaSetting.volK2
    exact ENNReal.toReal_pos hK.2.2.1.ne' hK.2.2.2.ne
  have hc := poincareConstant_pos X Y u
  have hc' := poincareConstant_pos X Y u'
  unfold Formalism.L2.SG.TermOp.scl
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos hc hc'))) hV

theorem amplitude_lower_bound_real {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hSt : Formalism.MainNotions.S.Cnt.Stand D u u') (hi : ∀ v, i0 v = i0' v) (hNuP : Formalism.L2.SG.RealObj.NuQPin X u u' νq)
    (hVP : Formalism.L2.SG.VolPin.VolumeOddGeneric) (hg3 : ∀ i, 3 ≤ D.host.g i) :
    Formalism.L2.SG.Pf.RowForm.ClassAbs.AmpValLowerC X Y u u'
      (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) i0 i0' νq := by
  have hPH : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') := Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
  have hi' : i0' = i0 := funext fun v => (hi v).symm
  subst hi'
  let κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ := fun _ => 0
  have hAtS : ∀ t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w :=
    fun t hG hr => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' t hG hr
  have hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.cell_point_unique_of_term_fun (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  have hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.normRepExists_of (Formalism.L2.SG.Pf.NormRepX.norm_representative_holds D u u' hPH)
      (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  have hLD : Formalism.L2.SG.Pf.RowForm.LiftDecompC X Y u u' κ :=
    Formalism.L2.SG.Pf.RowForm.liftDecompC_of_real (κ := κ) (h := Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of (hAt := hAtS))
  have hFT := Formalism.L2.SG.Pf.formula_transport_of_condition (κ := κ) (hP := hNuP) (hV := hVP) (hg3 := hg3) (hPH := hPH)
    (hRC := Formalism.L2.SG.Pf.RelChar.relCharC_holds) (hLD := hLD) (hAt := Formalism.L2.SG.Pf.LiftedPhaseAgreement.liftAtSomeC_holds X Y u u' κ)
    (hNR := hNR) (hCPU := hCU)
  have hDF : Formalism.L2.SG.Pf.RowForm.DFrameAtS X u u' i0' i0' 1 := Formalism.L2.SG.Pf.Carrier.dual_frame_at_places X u u' 1 i0'
  have hNF := Formalism.L2.SG.Pf.RowForm.normalFormC_all (hAtS := hAtS) (hTP := fun t w h => Formalism.L2.SG.WConst.atPt_totPos t w h)
    (hCU := hCU) (hDF := hDF) (hPT := Formalism.L2.SG.Pf.LiftedPhaseAgreement.phaseTieC_holds (κ := κ) (hP := hPH)) (hFT := hFT)
  refine Formalism.L2.SG.Pf.ampValLowerC_of X Y u u' _ i0' i0' νq κ hNF
    (fun t w h => Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' _ _ t w h) ?_
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := by
    unfold Formalism.L2.SG.HidaSetting.HidaSetting.volK2
    exact ENNReal.toReal_pos hK.2.2.1.ne' hK.2.2.2.ne
  have hc := poincareConstant_pos X Y u
  have hc' := poincareConstant_pos X Y u'
  unfold Formalism.L2.SG.TermOp.scl
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos hc hc'))) hV

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

theorem ampValLowerAll_of (hVP : Formalism.L2.SG.VolPin.VolPinGC) : AmpValLowerAll := by
  intro D T u u' i0 i0' νq _ hSt _ hi _ hNuP
  exact Formalism.L2.SG.Pf.ampValLowerC_vR T.X T.Y u u' i0 i0' νq hSt hi hNuP hVP

theorem rowsSumC_of' (hFC : FormulaC) (hVP : Formalism.L2.SG.VolPin.VolPinGC) : RowsSumC :=
  rowsSumC_of hFC (ampValLowerAll_of hVP)

theorem rowsSum_of_formula_volume (hFC : FormulaC) (hVP : Formalism.L2.SG.VolPin.VolumeOddGeneric) : RowsSumC := by
  intro D T u u' i0 i0' νq Lsp κ hne hSt hCT hg3 hk hcong hi hPR hNu hRL
  have hWD : Formalism.L2.SG.WuDecay.WuDecay T.X := hCT.2.2.2.2.1
  have hAbs : (T.Y.tO u u').AbsConv :=
    Formalism.L2.SG.Pf.absConvC_outright D T.X T.Y u u'
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u' (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Pf.fundExistsC_holds D T.X T.Y u u')
      (Formalism.L2.SG.Pf.KernelOfEmbedding.ooIntAll_of (Y := T.Y) hWD u u')
  have hL := Formalism.L2.SG.Pf.liftOntoC_of (fun D => Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) D T.X T.Y u u'
  have hAF : Formalism.L2.SG.PairVal.AutFin D (T.X.Fu u) (T.Y.what₂ u) := fun Λ hΛ =>
    _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u).A.T_prime.pos (T.X.Fu u) Λ ((T.Y.rowsOK u).1 Λ hΛ)
  have hAF' : Formalism.L2.SG.PairVal.AutFin D (T.X.Fu u') (T.Y.what₂ u') := fun Λ hΛ =>
    _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u').A.T_prime.pos (T.X.Fu u') Λ ((T.Y.rowsOK u').1 Λ hΛ)
  have hLT : Formalism.L2.SG.Pf.LocCP.LocTied D := by
    obtain ⟨_, _, _, _, _, _, _, hL⟩ := hCT.2.2.2.2.2.2.1
    exact hL
  have hnc : 0 < Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p :=
    mul_pos (hFC D T u u' Lsp hLT hSt hcong).1 (tprod_alpD_pos D hk u u')
  exact Formalism.L2.SG.RowsAbsX.rowsSum_of_val _ κ _ i0 i0' (T.Y.FN u) (T.Y.FN u') νq hAbs hL
    (Formalism.L2.SG.Pf.amplitude_lower_bound_real T.X T.Y u u' i0 i0' νq hSt hi hNu hVP hg3) hAF hAF' hnc

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
