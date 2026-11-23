import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserHaarRootCoordinatesLeLebesgueStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegerPointsCoverRealPointsRootCoordinatesStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory in

theorem GlobalTheory.LoopVol.packing_pinned {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (s : TT Y u u')
    {γw g g' : X.B.I.Ginf} {μw : Measure X.B.I.Ginf} (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hdec : s.pt.1 = g * γw * g'⁻¹) (hH : IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw)
    {K B : Set X.B.I.Ginf} (hK : Formalism.L2.SG.LoopTerm.IsFundR s K) (hB : MeasurableSet B)
    (hcov : ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset s, ∃ q ∈ Formalism.L2.SG.TermOp.ROinf s, q * r ∈ B) :
    (μw.map fun y => g * y * g⁻¹) K ≤ (μw.map fun y => g * y * g⁻¹) B := by
  obtain ⟨-, -, hconc, hinvw⟩ := hH
  obtain ⟨hKm, hKu⟩ := hK
  haveI := Formalism.L2.SG.TermOp.Vanish.ROsub_countable X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin
  set Γ := Formalism.L2.SG.TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin with hΓ
  set μR := μw.map fun y => g * y * g⁻¹ with hμR
  have hcm : Measurable fun y : X.B.I.Ginf => g * y * g⁻¹ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hRm : MeasurableSet (Formalism.L2.SG.TermOp.Vanish.Rset s) :=
    (Formalism.L2.SG.Pf.rClosedC_holds D X Y u u' s).measurableSet
  have hRc : μR (Formalism.L2.SG.TermOp.Vanish.Rset s)ᶜ = 0 := by
    rw [hμR, Measure.map_apply hcm hRm.compl]
    exact measure_mono_null (fun y hy hySt => hy (Formalism.L2.SG.LoopTerm.stInf_conj hg hg' hdec hySt)) hconc
  have hinv : ∀ q ∈ Γ, μR.map (fun x => q * x) = μR := by
    intro q hq
    have hq' := Formalism.L2.SG.LoopTerm.stInf_conj_inv hg hg' hdec (Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset s hq)
    rw [hμR, Measure.map_map (measurable_const_mul q) hcm]
    have e : (fun x => q * x) ∘ (fun y => g * y * g⁻¹) =
        (fun y => g * y * g⁻¹) ∘ (fun y => (g⁻¹ * q * g) * y) := by
      funext y; simp only [Function.comp]; group
    rw [e, ← Measure.map_map hcm (measurable_const_mul _), hinvw _ hq']
  have hpre : ∀ q ∈ Γ, ∀ C, MeasurableSet C → μR ((fun x => q * x) ⁻¹' C) = μR C := by
    intro q hq C hC
    rw [← Measure.map_apply (measurable_const_mul q) hC, hinv q hq]
  have h1 : μR K ≤ ∑' q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) := by
    calc μR K = μR (K ∩ Formalism.L2.SG.TermOp.Vanish.Rset s) := (measure_inter_conull hRc).symm
      _ ≤ μR (⋃ q : Γ, K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) := by
          refine measure_mono fun r hr => ?_
          obtain ⟨q, hq, hqr⟩ := hcov r hr.2
          exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hr.1, hqr⟩
      _ ≤ _ := measure_iUnion_le _
  have h2 : ∀ q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) =
      μR (B ∩ (fun x => ((q⁻¹ : Γ) : X.B.I.Ginf) * x) ⁻¹' K) := by
    intro q
    have hC : MeasurableSet (B ∩ (fun x => ((q⁻¹ : Γ) : X.B.I.Ginf) * x) ⁻¹' K) :=
      hB.inter (hKm.preimage (measurable_const_mul _))
    rw [← hpre q q.2 _ hC]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.coe_inv, inv_mul_cancel_left]
    exact and_comm
  have h3 := Formalism.L2.SG.Pf.FormAllPf.decomp μR (Formalism.L2.SG.TermOp.Vanish.Rset s) hRc Γ B K hB hKm hKu
  have h4 : ∑' q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) = μR B := by
    rw [h3]
    simp_rw [h2]
    exact (Equiv.inv Γ).tsum_eq (fun q => μR (B ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K))
  exact h1.trans_eq h4

theorem GlobalTheory.LoopVol.ka_div_le_one {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (hSt : Formalism.MainNotions.S.Cnt.Stand D u u') :
    D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 := by
  have hrd := GlobalTheory.RealPlaces.one_le_rdE D
  have hg0 := hSt.2.2.2.2.2.2.2.1.two_le
  have hg1 := hSt.2.2.2.2.2.2.2.2.1.two_le
  have h0 : (2 : ℝ) ≤ (D.host.g 0 : ℝ) := by exact_mod_cast hg0
  have h1 : (2 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast hg1
  have hgR : (4 : ℝ) ≤ (X.B.g : ℝ) := by rw [X.g_eq]; push_cast; nlinarith
  have e : D.host.ka / (X.B.g : ℝ) / Real.pi = 2 / (D.host.rdE * X.B.g) := by
    rw [show D.host.ka = Real.pi / (D.host.rdE / 2) from rfl]
    have : (0 : ℝ) < D.host.rdE := by linarith
    have : (0 : ℝ) < (X.B.g : ℝ) := by linarith
    field_simp
  rw [e, div_le_one (by positivity)]
  nlinarith

theorem GlobalTheory.LoopVol.covolume_le_cover : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (μR : MeasureTheory.Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.VolPin.IsPinnedR s w μR → Formalism.L2.SG.LoopTerm.IsFundR s K → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet Ω → (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → μR K ≤ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  intro Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w μR K hat hPin hK L U hL hU hZ Ω hΩ hcov
  obtain ⟨γw, sf, s', μw, hrep, hsf, hs', hdec, hμwH, hμwS, rfl⟩ := hPin
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.T.integerPoints_cover_realPoints_rootCoordinates Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w γw sf s' hat hrep hsf hs' hdec
    L U hL hU hZ Ω hcov
  have hTΩ : MeasurableSet (T ⁻¹' Ω) := hT.measurable hΩ
  have hBm : MeasurableSet (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' (T ⁻¹' Ω)) :=
    (GlobalTheory.LoopVol.ratCoord_cont X u' w γw sf).measurable hTΩ
  have hka := GlobalTheory.LoopVol.ka_div_le_one X hH.2.1
  calc (μw.map fun y => sf * y * sf⁻¹) K
      ≤ (μw.map fun y => sf * y * sf⁻¹) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' (T ⁻¹' Ω)) :=
        GlobalTheory.LoopVol.packing_pinned s hsf hs' hdec hμwH hK hBm hTc
    _ ≤ MeasureTheory.volume (T ⁻¹' Ω) * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) :=
        GlobalTheory.T.stabiliserHaar_rootCoordinates_le_lebesgue D X u u' w γw sf μw hμwH hμwS hka _ hTΩ
    _ = MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
        rw [hT.measure_preimage hΩ.nullMeasurableSet]

end
