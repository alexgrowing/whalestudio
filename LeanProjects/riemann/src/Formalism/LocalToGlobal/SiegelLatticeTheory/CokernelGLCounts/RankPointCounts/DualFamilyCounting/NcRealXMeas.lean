import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstPf

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem embQ (hF : IsFrameJ ε e f wf z0) :
    MeasurableEmbedding (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) :=
  cM_measEmb (ε := ε) (A := Qi ε e f wf z0) (B := Qm e f wf z0) (A' := Qm e f wf z0) (B' := Qi ε e f wf z0)
    (Qm_mul_Qi hF) (Qm_mul_Qi hF)

theorem Qm_e (a : Fin r) : Qm e f wf z0 *ᵥ bvec (eI k r a) = e a := by rw [Qm_mulVec_bvec, colQ_eI]

theorem Qm_f (a : Fin r) : Qm e f wf z0 *ᵥ bvec (esI k r a) = f a := by rw [Qm_mulVec_bvec, colQ_esI]

theorem conj_fix (hF : IsFrameJ ε e f wf z0) {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {v : Fin (2 * r + k + 1) → ℂ} (hv : s *ᵥ v = v) :
    (Qm e f wf z0 * s * Qi ε e f wf z0) *ᵥ (Qm e f wf z0 *ᵥ v) = Qm e f wf z0 *ᵥ v := by
  rw [Matrix.mulVec_mulVec]
  have e1 : Qm e f wf z0 * s * Qi ε e f wf z0 * Qm e f wf z0 = Qm e f wf z0 * s := by
    rw [Matrix.mul_assoc (Qm e f wf z0 * s), Qi_mul_Qm hF, Matrix.mul_one]
  rw [e1, ← Matrix.mulVec_mulVec, hv]

theorem measW_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} {μH : Measure (Formalism.REAL.UJ ε)}
    (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH) :
    Formalism.MainNotions.S.IsHaarOn (UWset k r zB) (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
  have emb := embQ hF
  obtain ⟨hsf, hne, hcon, hinv⟩ := hH
  haveI := hsf
  refine ⟨emb.sigmaFinite_map, (Measure.map_ne_zero_iff emb.measurable.aemeasurable).mpr hne, ?_, ?_⟩
  · rw [emb.map_apply]
    refine measure_mono_null (fun g hg => ?_) hcon
    intro hgH
    apply hg
    exact conj_mem_UWset hF rfl (uMat_mem g) (fun a => (hgH.1 a).1) (fun a => (hgH.1 a).2) hgH.2
  · intro s hs
    have ht := conjQ_UJ hF hs.1
    set t := toUJ (Qm e f wf z0 * s * Qi ε e f wf z0) ht
    have htH : t ∈ Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB) := by
      show (∀ a, uMat t *ᵥ e a = e a ∧ uMat t *ᵥ f a = f a) ∧ uMat t *ᵥ (Qm e f wf z0 *ᵥ zB) = Qm e f wf z0 *ᵥ zB
      rw [uMat_toUJ]
      refine ⟨fun a => ⟨?_, ?_⟩, conj_fix hF hs.2.2⟩
      · rw [← Qm_e (e := e) (f := f) (wf := wf) (z0 := z0) a]; exact conj_fix hF (hs.2.1 a).1
      · rw [← Qm_f (e := e) (f := f) (wf := wf) (z0 := z0) a]; exact conj_fix hF (hs.2.1 a).2
    rw [Measure.map_map (measurable_lmulM s) emb.measurable]
    have hfun : lmulM s ∘ cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) =
        cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) ∘ (fun g : Formalism.REAL.UJ ε => t * g) := by
      funext g
      simp only [Function.comp, lmulM_cM]
      unfold cM
      rw [uMat_mul, uMat_toUJ]
      simp only [← Matrix.mul_assoc, Qi_mul_Qm hF, Matrix.one_mul]
      try rfl
    rw [hfun, ← Measure.map_map emb.measurable (measurable_const_mul t), hinv t htH]

theorem measN_of (hF : IsFrameJ ε e f wf z0) (κ : ℝ) :
    (ENNReal.ofReal κ • refN ε e f wf z0).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ) := by
  have emb := embQ hF
  rw [Measure.map_smul, refN, emb.map_comap, Jac.haarLie_eq_smul (Nset k r) (ENNReal.ofReal κ)]
  congr 1
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have hc : (Formalism.MainNotions.S.haarLie (Nset k r) 1) {x | Matrix.of x ∉ Nset k r} = 0 := Jac.nilradical_measure_is_haar.2.2.1
  refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hc)
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro hxN
  apply hx
  have hU := conjQ_UJ hF hxN.1
  refine ⟨toUJ _ hU, ?_⟩
  show Qi ε e f wf z0 * uMat (toUJ _ hU) * Qm e f wf z0 = x
  rw [uMat_toUJ, Qi_Qm_conj hF]
  rfl

theorem haarN_of (κ : ℝ) (hκ : 0 < κ) : Formalism.MainNotions.S.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) :=
  Formalism.MainNotions.BridgeCSB.haarLieN k r _ (ENNReal.ofReal_pos.2 hκ).ne' ENNReal.ofReal_ne_top

theorem psi_mul (hF : IsFrameJ ε e f wf z0) (n h : Formalism.REAL.UJ ε) :
    cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) (n * h) =
      Jac.mm (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) n) (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) h) :=
  (cM_comp_mul hF (Qm e f wf z0) n h).symm

theorem measS_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB)
    (hT : 0 < Tz k r zB) {μH : Measure (Formalism.REAL.UJ ε)} (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH)
    (κ : ℝ) (hκ : 0 < κ) :
    (muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      Formalism.MainNotions.S.muS (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)))
        (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) := by
  have emb := embQ hF
  have hW := measW_of hF hH
  have hN := haarN_of (k := k) (r := r) κ hκ
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  set μW := μH.map Ψ with hμW
  set μN := Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ) with hμN
  set μN' := ENNReal.ofReal κ • refN ε e f wf z0 with hμN'
  haveI : SigmaFinite μH := hH.1
  haveI : SigmaFinite μW := hW.1
  haveI : SigmaFinite μN := hN.1
  have hNmap : μN'.map Ψ = μN := measN_of hF κ
  have hWB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ hN
  apply Measure.ext_of_lintegral
  intro g hg
  have hgm : Measurable fun p : Mt k r × Mt k r => g (Jac.mm p.1 p.2) := hg.comp Jac.measurable_mt_mul
  rw [Jac.lintegral_muS μW μN hg, lintegral_map hg emb.measurable]
  have hmul : Measurable fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => p.1 * p.2 := measurable_mul
  have hgΨ : Measurable fun a : Formalism.REAL.UJ ε => g (Ψ a) := hg.comp emb.measurable
  rw [show muSL μH μN' = (μN'.prod μH).map (fun p => p.1 * p.2) from rfl,
    lintegral_map hgΨ hmul,
    lintegral_prod (fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => g (Ψ (p.1 * p.2))) (hgΨ.comp hmul).aemeasurable]
  have hpm : ∀ n h : Formalism.REAL.UJ ε, Ψ (n * h) = Jac.mm (Ψ n) (Ψ h) := psi_mul hF
  simp only [hpm]
  have step1 : ∀ n : Formalism.REAL.UJ ε, ∫⁻ h, g (Jac.mm (Ψ n) (Ψ h)) ∂μH = ∫⁻ y, g (Jac.mm (Ψ n) y) ∂μW := by
    intro n
    rw [hμW, emb.lintegral_map]
  simp_rw [step1]
  rw [← emb.lintegral_map (μ := μN') (f := fun x => ∫⁻ y, g (Jac.mm x y) ∂μW), hNmap]
  rw [lintegral_lintegral_swap (f := fun x y => g (Jac.mm x y)) hgm.aemeasurable]

  have hconc : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r zB := by
    have h0 : μW {x | Matrix.of x ∉ UWset k r zB} = 0 := hW.2.2.1
    exact ae_iff.2 h0
  refine lintegral_congr_ae ?_
  filter_upwards [hconc] with h hh
  have hd : IsUnit (Matrix.of h).det := JL.RI.det_unit_of_UH hh.1
  have hhi : (Matrix.of h)⁻¹ ∈ UWset k r zB := JL.RI.inv_mem_UW hh
  have hc : μN.map (conjM (k := k) (r := r) (Matrix.of h)⁻¹) = μN :=
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r zB μN hz hT hWB _ hhi
  conv_rhs => rw [← hc]
  have hmh : Measurable fun n : Mt k r => g (Jac.mm h n) := hgm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map hmh (Jac.meas_conjM _)]
  refine lintegral_congr fun x => ?_
  congr 1
  show Jac.mm x h = Jac.mm h (conjM (Matrix.of h)⁻¹ x)
  funext i j
  show (Matrix.of x * Matrix.of h) i j = (Matrix.of h * ((Matrix.of h)⁻¹ * Matrix.of x * ((Matrix.of h)⁻¹)⁻¹)) i j
  rw [Matrix.nonsing_inv_nonsing_inv _ hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
    Matrix.one_mul]

theorem haarW_B (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB) (hT : 0 < Tz k r zB)
    {μH : Measure (Formalism.REAL.UJ ε)} (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH)
    (hfin : μH Set.univ ≠ ⊤) :
    Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r zB) (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
  have emb := embQ hF
  have hW := measW_of hF hH
  obtain ⟨μ0, h0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r zB hz hT
  have hνfin : ∀ K, (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) K < ⊤ := fun K =>
    lt_of_le_of_lt (measure_mono (Set.subset_univ K)) (by rw [emb.map_apply, Set.preimage_univ]; exact hfin.lt_top)
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (UWset k r zB) μ0 _ (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r zB) h0
    hW.2.2.1 hW.2.2.2 (fun K _ => hνfin K)
  exact ⟨hW.2.2.1, hW.2.2.2, fun a ha => by rw [hc, Measure.map_smul, h0.right a ha], fun K _ => hνfin K, hW.2.1⟩

theorem rightX_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB)
    (hT : 0 < Tz k r zB) {μH : Measure (Formalism.REAL.UJ ε)}
    (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH) (hfin : μH Set.univ ≠ ⊤)
    (κ : ℝ) (hκ : 0 < κ) (s : Formalism.REAL.UJ ε) (hs : s ∈ SLoc ε e (Qm e f wf z0 *ᵥ zB)) :
    (muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map (fun x => x * s) =
      muSL μH (ENNReal.ofReal κ • refN ε e f wf z0) := by
  have emb := embQ hF
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  set μS := muSL μH (ENNReal.ofReal κ • refN ε e f wf z0) with hμS
  have hN := haarN_of (k := k) (r := r) κ hκ
  have hWB := haarW_B hF hz hT hH hfin
  have hNB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) :=
    Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ hN
  have hQinv : (Qm e f wf z0)⁻¹ = Qi ε e f wf z0 := Matrix.inv_eq_left_inv (Qi_mul_Qm hF)
  have hdet : IsUnit (Qm e f wf z0).det := Matrix.isUnit_det_of_left_inverse (Qi_mul_Qm hF)
  set sM : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Qi ε e f wf z0 * uMat s * Qm e f wf z0 with hsM
  have hSs : sM ∈ Sset k r zB := by
    have := (JL.setCorr_holds r k ε e (Qm e f wf z0 *ᵥ zB) zB (Qm e f wf z0) (gramQ hF) hdet
      (fun a => Qm_e (f := f) (wf := wf) (z0 := z0) a) hz rfl hT s).1 hs
    rw [hQinv] at this
    exact this
  have hmeas : Measurable fun x : Formalism.REAL.UJ ε => x * s := measurable_mul_const s
  have hfun : Ψ ∘ (fun x => x * s) = Formalism.FourierDecayAlt.B.rmulF sM ∘ Ψ := by
    funext x
    show (Qi ε e f wf z0 * uMat (x * s) * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      (Qi ε e f wf z0 * uMat x * Qm e f wf z0) * (Qi ε e f wf z0 * uMat s * Qm e f wf z0)
    rw [uMat_mul]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (Qi ε e f wf z0 * uMat x) (Qm e f wf z0) (Qi ε e f wf z0), Qm_mul_Qi hF, Matrix.mul_one]
  have key : (μS.map (fun x => x * s)).map Ψ = μS.map Ψ := by
    rw [Measure.map_map emb.measurable hmeas, hfun,
      ← Measure.map_map (JL.RI.meas_rmul (k := k) (r := r) _) emb.measurable, hμS, measS_of hF hz hT hH κ hκ]
    exact JL.RI.muS_right hz hT hWB hNB _ hSs
  rw [← emb.comap_map (μS.map (fun x => x * s)), key, emb.comap_map]

end Formalism.L2.SG.Pf.NcReal.JX
