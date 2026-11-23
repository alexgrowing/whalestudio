import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProdExactHolds

noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem isFrameJ_of {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
    {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z : Fin (2 * r + k + 1) → ℂ} {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) : IsFrameJ ε e f wf (z0v T z) := by
  have hl : ∀ (x y : Fin (2 * r + k + 1) → ℂ) (c : ℂ), hJ ε (c • x) y = star c * hJ ε x y := by
    intro x y c
    simp [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul]
  have hr : ∀ (x y : Fin (2 * r + k + 1) → ℂ) (c : ℂ), hJ ε x (c • y) = c * hJ ε x y := by
    intro x y c
    simp [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul]
  have hsc : star ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  have key : ((Real.sqrt T)⁻¹ * ((Real.sqrt T)⁻¹ * -T) : ℝ) = -1 := by
    rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hT.le, mul_neg, inv_mul_cancel₀ hT.ne']
  refine ⟨hee, hff, hef, ?_, ?_, ?_, hww, hew, hfw, ?_⟩
  · intro a
    rw [Formalism.L2.SG.Pf.WFL.z0v, hr, hez, mul_zero]
  · intro a
    rw [Formalism.L2.SG.Pf.WFL.z0v, hr, hfz, mul_zero]
  · rw [Formalism.L2.SG.Pf.WFL.z0v, hl, hr, hzz, hsc]
    exact_mod_cast key
  · intro a
    rw [Formalism.L2.SG.Pf.WFL.z0v, hl, hzw, mul_zero]

theorem hLoc_eq {n r : ℕ} (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    Formalism.L2.SG.Pf.NcReal.HLoc ε e f z = Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc ε e f z := by
  ext s
  simp only [Formalism.L2.SG.Pf.NcReal.HLoc, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc, Set.mem_setOf_eq, forall_and,
    and_assoc]

theorem compact_HLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (wf : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) : IsCompact (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z) := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have hemb := cM_closedEmb (ε := ε) (A := Qi ε e f wf (z0v T z)) (B := Qm e f wf (z0v T z))
    (A' := Qm e f wf (z0v T z)) (B' := Qi ε e f wf (z0v T z)) (Qm_mul_Qi hFJ) (Qm_mul_Qi hFJ)
  have hW : IsCompact (UWset k r (zBv k r T) : Set (Mt k r)) :=
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r (zBv k r T) (inWb_zB T) (by rw [Tz_zB hT.le]; exact hT)
  have hK := hemb.isCompact_preimage hW
  have hcl : IsClosed (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z) := by
    rw [hLoc_eq]
    exact NilradicalHermitianFrames.NH.HG_closed ε e f z
  refine hK.of_isClosed_subset hcl fun g hg => ?_
  exact conj_mem_UWset hFJ (Qm_zB hT z) (uMat_mem g) (fun a => (hg.1 a).1) (fun a => (hg.1 a).2) hg.2

theorem pi_smul_factors {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  haveI : ∀ i, SigmaFinite (c i • μ i) := fun i =>
    ⟨⟨⟨spanningSets (μ i), fun _ => Set.mem_univ _, fun n => by
        rw [Measure.smul_apply, smul_eq_mul]
        exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top (hc i) (measure_spanningSets_lt_top (μ i) n).ne),
      iUnion_spanningSets (μ i)⟩⟩⟩
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

theorem isHaarLoc_smul {n : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)} {μ : Measure (Formalism.REAL.UJ ε)}
    (h : IsHaarLoc S μ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) : IsHaarLoc S (c • μ) := by
  unfold Formalism.L2.SG.RealObj.IsHaarLoc at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  haveI := h1
  refine ⟨⟨⟨⟨spanningSets μ, fun _ => Set.mem_univ _, fun n => ?_, iUnion_spanningSets μ⟩⟩⟩, ?_, ?_, ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top hc (measure_spanningSets_lt_top μ n).ne)
  · intro h0
    apply h2
    ext s _
    simpa [hc0] using congrArg (fun m : Measure (Formalism.REAL.UJ ε) => m s) h0
  · simp [h3]
  · intro s hs
    rw [Measure.map_smul, h4 s hs]

end Gen

section HidaSetting

variable {D : D7} (X : HidaSetting D)

theorem nX : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  rw [X.n_eq]
  have hm := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

def refNX (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  refNg (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (z0v (Tw u) (ProductExactness.zV X u v))

section Facts

variable (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)

theorem fX_ee : ∀ a b, hJ (X.B.I.ε v) (eV X v a) (eV X v b) = 0 := fun a b =>
  (ProductExactness.hJ_X X v _ _).trans (by rw [X.ee]; simp)
theorem fX_ff : ∀ a b, hJ (X.B.I.ε v) (ProductExactness.pV X v a) (ProductExactness.pV X v b) = 0 := fun a b =>
  (ProductExactness.hJ_X X v _ _).trans (by rw [X.ff]; simp)
theorem fX_ef : ∀ a b, hJ (X.B.I.ε v) (eV X v a) (ProductExactness.pV X v b) = if a = b then 1 else 0 := fun a b =>
  (ProductExactness.hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
theorem fX_ww : ∀ a b, hJ (X.B.I.ε v) (X.wfr u v a) (X.wfr u v b) = if a = b then 1 else 0 := X.wfr_on u v
theorem fX_ew : ∀ c a, hJ (X.B.I.ε v) (eV X v c) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).1
theorem fX_fw : ∀ c a, hJ (X.B.I.ε v) (ProductExactness.pV X v c) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).2
theorem fX_ez : ∀ a, hJ (X.B.I.ε v) (eV X v a) (ProductExactness.zV X u v) = 0 := (ProductExactness.frameLoc_X X u u v).ez
theorem fX_fz : ∀ a, hJ (X.B.I.ε v) (ProductExactness.pV X v a) (ProductExactness.zV X u v) = 0 := fun a =>
  (ProductExactness.hJ_X X v _ _).trans (by rw [(X.zu_orth u a).2]; simp)
theorem frame_real_z_z_eq_neg : hJ (X.B.I.ε v) (ProductExactness.zV X u v) (ProductExactness.zV X u v) = -((Tw u : ℝ) : ℂ) :=
  (ProductExactness.frameLoc_X X u u v).zz
theorem fX_zw : ∀ a, hJ (X.B.I.ε v) (ProductExactness.zV X u v) (X.wfr u v a) = 0 := fun a => (X.wfr_perp u v a).2

end Facts

theorem muNv_eq (u w : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ∃ d : ℝ≥0∞, d ≠ 0 ∧ d ≠ ⊤ ∧ ProductExactness.muNv X w v = d • refNX X u v := by
  have hR := refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
    (ProductExactness.zV X w v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X w v)
  obtain ⟨r1, r2, r3, r4⟩ := hR
  obtain ⟨⟨m1, m2, m3, m4⟩, -⟩ := ProductExactness.muNv_haar X w v
  haveI : SigmaFinite (refNX X u v) := r1
  exact ProductExactness.PiM.uniq_on_closed (ProductExactness.NGv X w v) (NilradicalHermitianFrames.NH.NG_closed _ _ _) _ _ m3 r3 m4 r4 m2 r2

theorem muHv_mass (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ProductExactness.muHv X u v Set.univ ≠ 0 ∧ ProductExactness.muHv X u v Set.univ ≠ ⊤ := by
  obtain ⟨⟨m1, m2, m3, m4⟩, m5⟩ := ProductExactness.muHv_haar X u v
  have hK := compact_HLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
    (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
  rw [hLoc_eq] at hK
  refine ⟨fun h0 => m2 (Measure.measure_univ_eq_zero.1 h0), ?_⟩
  have hsplit : ProductExactness.muHv X u v Set.univ ≤
      ProductExactness.muHv X u v (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v)) +
        ProductExactness.muHv X u v (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v))ᶜ := by
    rw [← Set.union_compl_self (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v)
      (ProductExactness.zV X u v))]
    exact measure_union_le _ _
  have m3' : ProductExactness.muHv X u v
      (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v))ᶜ = 0 := m3
  rw [m3', add_zero] at hsplit
  exact (lt_of_le_of_lt hsplit (hK.measure_lt_top)).ne

end HidaSetting

def CovolRef : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' →
      ((Measure.pi (refNX X u)) FdN).toReal * ((Measure.pi (refNX X u)) FdN').toReal =
        |(NumberField.discr X.B.I.F : ℝ)| ^ eDF D.R.k D.R.rS

theorem placeSplit_of (hJG : JacGauge) (hC : CovolRef) : PlaceSplit := by
  classical
  intro D X hb FdN FdN' u u' ψ hHyp _ _ hGd
  obtain ⟨v0⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega

  obtain ⟨κN, hκN0, hκNT, hN⟩ := ProductExactness.muN_eq X u
  obtain ⟨κN', hκN'0, hκN'T, hN'⟩ := ProductExactness.muN_eq X u'
  choose d hd0 hdT hd using fun v => muNv_eq X u u v
  choose d' hd'0 hd'T hd' using fun v => muNv_eq X u u' v
  set cN : InfinitePlace X.B.I.F → ℝ≥0∞ := fun v => (if v = v0 then κN else 1) * d v with hcN
  set cN' : InfinitePlace X.B.I.F → ℝ≥0∞ := fun v => (if v = v0 then κN' else 1) * d' v with hcN'
  have hcT : ∀ v, cN v ≠ ⊤ := fun v => ENNReal.mul_ne_top (by split_ifs <;> simp [hκNT]) (hdT v)
  have hcT' : ∀ v, cN' v ≠ ⊤ := fun v => ENNReal.mul_ne_top (by split_ifs <;> simp [hκN'T]) (hd'T v)
  have hc0 : ∀ v, cN v ≠ 0 := fun v => mul_ne_zero (by split_ifs <;> simp [hκN0]) (hd0 v)
  have hc0' : ∀ v, cN' v ≠ 0 := fun v => mul_ne_zero (by split_ifs <;> simp [hκN'0]) (hd'0 v)
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
      (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X u v)).1
  have hprod : ∀ (κ0 : ℝ≥0∞) (dd : InfinitePlace X.B.I.F → ℝ≥0∞), (∀ v, dd v ≠ ⊤) → κ0 ≠ ⊤ →
      κ0 • Measure.pi (fun v => dd v • refNX X u v) =
        Measure.pi (fun v => ((if v = v0 then κ0 else 1) * dd v) • refNX X u v) := by
    intro κ0 dd hddT hκ0
    rw [pi_smul_factors _ dd hddT, pi_smul_factors _ _ (fun v => ENNReal.mul_ne_top
      (by split_ifs <;> simp [hκ0]) (hddT v)), smul_smul, Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hmuN : X.muN u = Measure.pi (fun v => cN v • refNX X u v) := by
    have he : ProductExactness.muNv X u = fun v => d v • refNX X u v := funext hd
    rw [hN, he]
    exact hprod κN d hdT hκNT
  have hmuN' : X.muN u' = Measure.pi (fun v => cN' v • refNX X u v) := by
    have he : ProductExactness.muNv X u' = fun v => d' v • refNX X u v := funext hd'
    rw [hN', he]
    exact hprod κN' d' hd'T hκN'T

  obtain ⟨κH, hκH0, hκHT, hH⟩ := ProductExactness.muH_eq X u
  obtain ⟨κH', hκH'0, hκH'T, hH'⟩ := ProductExactness.muH_eq X u'
  set μH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => (if v = v0 then κH else 1) • ProductExactness.muHv X u v with hμH
  set μH' : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => (if v = v0 then κH' else 1) • ProductExactness.muHv X u' v
    with hμH'
  have hsH : ∀ v, (if v = v0 then κH else 1) ≠ 0 ∧ (if v = v0 then κH else 1) ≠ ⊤ := fun v => by
    split_ifs <;> simp [hκH0, hκHT]
  have hsH' : ∀ v, (if v = v0 then κH' else 1) ≠ 0 ∧ (if v = v0 then κH' else 1) ≠ ⊤ := fun v => by
    split_ifs <;> simp [hκH'0, hκH'T]
  have hmuH : X.muH u = Measure.pi μH := by
    have hp : (∏ v, (if v = v0 then κH else 1 : ℝ≥0∞)) = κH := by simp
    rw [hH, hμH, pi_smul_factors _ _ (fun v => (hsH v).2), hp]
  have hmuH' : X.muH u' = Measure.pi μH' := by
    have hp : (∏ v, (if v = v0 then κH' else 1 : ℝ≥0∞)) = κH' := by simp
    rw [hH', hμH', pi_smul_factors _ _ (fun v => (hsH' v).2), hp]
  have hHaarH : ∀ v, IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u v)) (μH v) :=
    fun v => by
      rw [hLoc_eq]
      exact isHaarLoc_smul (ProductExactness.muHv_haar X u v).1 (hsH v).1 (hsH v).2
  have hHaarH' : ∀ v, IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (ProductExactness.zV X u' v))
      (μH' v) := fun v => by
    rw [hLoc_eq]
    exact isHaarLoc_smul (ProductExactness.muHv_haar X u' v).1 (hsH' v).1 (hsH' v).2
  have hmH : ∀ v, μH v Set.univ ≠ 0 ∧ μH v Set.univ ≠ ⊤ := fun v => by
    obtain ⟨h1, h2⟩ := muHv_mass X u v
    simp only [hμH, Measure.smul_apply, smul_eq_mul]
    exact ⟨mul_ne_zero (hsH v).1 h1, ENNReal.mul_ne_top (hsH v).2 h2⟩
  have hmH' : ∀ v, μH' v Set.univ ≠ 0 ∧ μH' v Set.univ ≠ ⊤ := fun v => by
    obtain ⟨h1, h2⟩ := muHv_mass X u' v
    simp only [hμH', Measure.smul_apply, smul_eq_mul]
    exact ⟨mul_ne_zero (hsH' v).1 h1, ENNReal.mul_ne_top (hsH' v).2 h2⟩

  refine ⟨fun v => cN v • refNX X u v, fun v => cN' v • refNX X u v, μH, μH',
    fun v => (μH v Set.univ).toReal, fun v => (μH' v Set.univ).toReal, fun v => (cN v).toReal,
    fun v => (cN' v).toReal, ((Measure.pi (refNX X u)) FdN).toReal, ((Measure.pi (refNX X u)) FdN').toReal,
    fun v => ProductExactness.sf_smul _ _ (hcT v), fun v => ProductExactness.sf_smul _ _ (hcT' v), fun v => (hHaarH v).1,
    fun v => (hHaarH' v).1, fun v => ⟨ENNReal.toReal_pos (hmH v).1 (hmH v).2, ENNReal.toReal_pos (hmH' v).1 (hmH' v).2,
      ENNReal.toReal_pos (hc0 v) (hcT v), ENNReal.toReal_pos (hc0' v) (hcT' v)⟩,
    hmuN, hmuN', hmuH, hmuH', fun v => (ENNReal.ofReal_toReal (hmH v).2).symm,
    fun v => (ENNReal.ofReal_toReal (hmH' v).2).symm, ?_, ?_, ?_, hC X hb FdN FdN' u u' hHyp⟩
  · intro v h hh
    have hP := placeStep hJG (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u' v) hk (ProductExactness.Tw_pos u) (ProductExactness.Tw_pos u') (fX_ee X v) (fX_ff X v) (fX_ef X v)
      (fX_ww X u v) (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
      (fX_ez X u' v) (fX_fz X u' v) (frame_real_z_z_eq_neg X u' v) (hGd v) (μH v) (μH' v) (hHaarH v) (hHaarH' v)
      _ _ (ENNReal.toReal_pos (hmH v).1 (hmH v).2) (ENNReal.toReal_pos (hmH' v).1 (hmH' v).2)
      (ENNReal.ofReal_toReal (hmH v).2).symm (ENNReal.ofReal_toReal (hmH' v).2).symm
      (cN v).toReal (cN' v).toReal (ENNReal.toReal_pos (hc0 v) (hcT v)) (ENNReal.toReal_pos (hc0' v) (hcT' v)) h hh
    rw [ENNReal.ofReal_toReal (hcT v), ENNReal.ofReal_toReal (hcT' v)] at hP
    exact hP
  · rw [hmuN, pi_smul_factors _ _ hcT, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_prod]
  · rw [hmuN', pi_smul_factors _ _ hcT', Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_prod]

theorem realBracket_of_jac (hJG : JacGauge) (hC : CovolRef) (hA : AprimeInf)
    (hG : ∀ (n : ℕ) (ε : Fin n → Bool), Formalism.MainNotions.S.Gauge.GaugeDens ε) : RealBracket :=
  realBracket_of Formalism.L2.SG.RealObj.InfCut.ProductExactness.ProdExact_holds hA (placeSplit_of hJG hC) hG

end Formalism.L2.SG.Pf.NcReal.JX
