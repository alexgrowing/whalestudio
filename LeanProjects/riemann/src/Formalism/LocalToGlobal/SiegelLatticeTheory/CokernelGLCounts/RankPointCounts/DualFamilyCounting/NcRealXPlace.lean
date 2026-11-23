import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealX
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXN

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

def refNg : {n r k : ℕ} → n = 2 * r + k + 1 → (ε : Fin n → Bool) → (Fin r → Fin n → ℂ) → (Fin r → Fin n → ℂ) →
    (Fin k → Fin n → ℂ) → (Fin n → ℂ) → Measure (Formalism.REAL.UJ ε)
  | _, _, _, rfl, ε, e, f, wf, z0 => refN ε e f wf z0

theorem refNg_rfl {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) :
    refNg rfl ε e f wf z0 = refN ε e f wf z0 := rfl

theorem muSL_smul {n : ℕ} {ε : Fin n → Bool} (μH μN : Measure (Formalism.REAL.UJ ε)) [SFinite μH] (c : ℝ≥0∞) :
    muSL μH (c • μN) = c • muSL μH μN := by
  unfold muSL; rw [Measure.prod_smul_left, Measure.map_smul]

theorem disint_smul_right {n r k : ℕ} {ε : Fin n → Bool} {T T' : ℝ} {μS μS' : Measure (Formalism.REAL.UJ ε)}
    {h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} {C c : ℝ} (hc : 0 < c) (hD : DisintLoc ε k T T' μS μS' h C) :
    DisintLoc ε k T T' μS (ENNReal.ofReal c • μS') h (C / c) := by
  intro φ hφ
  rw [hD φ hφ]
  refine setLIntegral_congr_fun (JL.measurableSet_goodLoc r T T') (fun x _ => ?_)
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul' hc.le]
  congr 2
  field_simp

theorem placeStep (hJG : JacGauge) {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool)
    (e f : Fin r → Fin n → ℂ) (wf : Fin k → Fin n → ℂ) (z z' : Fin n → ℂ) {T T' : ℝ} (hk : 1 ≤ k) (hT : 0 < T)
    (hT' : 0 < T') (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0)
    (hez' : ∀ a, hJ ε (e a) z' = 0) (hfz' : ∀ a, hJ ε (f a) z' = 0) (hzz' : hJ ε z' z' = -(T' : ℂ))
    (hG : Formalism.MainNotions.S.Gauge.GaugeDens ε) (μH μH' : Measure (Formalism.REAL.UJ ε))
    (hH : IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z) μH) (hH' : IsHaarLoc (Formalism.L2.SG.Pf.NcReal.HLoc ε e f z') μH')
    (a a' : ℝ) (ha : 0 < a) (ha' : 0 < a') (hma : μH Set.univ = ENNReal.ofReal a)
    (hma' : μH' Set.univ = ENNReal.ofReal a') (κ κ' : ℝ) (hκ : 0 < κ) (hκ' : 0 < κ')
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (hh : IsSecLoc ε 1 e z z' T T' h) :
    DisintLoc ε k T T' (muSL μH (ENNReal.ofReal κ • refNg hn ε e f wf (z0v T z)))
      (muSL μH' (ENNReal.ofReal κ' • refNg hn ε e f wf (z0v T z))) h
      (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
        ((T * T') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * (κ * κ'))) := by
  subst hn
  have hs : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ * T = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hsC : ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * (T : ℂ) = 1 := by exact_mod_cast hs
  have hFJ : IsFrameJ ε e f wf (z0v T z) :=
    { ee := hee, ff := hff, ef := hef
      ez := fun a => by rw [z0v, JL.hJ_smul_r, hez, mul_zero]
      fz := fun a => by rw [z0v, JL.hJ_smul_r, hfz, mul_zero]
      zz := by
        rw [z0v, JL.hJ_smul_l, JL.hJ_smul_r, hzz, Complex.conj_ofReal]
        linear_combination (-1 : ℂ) * hsC
      ww := hww, ew := hew, fw := hfw
      zw := fun a => by rw [z0v, JL.hJ_smul_l, hzw, mul_zero] }
  have hzB : inWb k r (zBv k r T) := inWb_zB T
  have hQzB : Qm e f wf (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  have hTzB : Tz k r (zBv k r T) = T := Tz_zB hT.le
  set zB' := Qi ε e f wf (z0v T z) *ᵥ z' with hzB'
  have hQzB' : Qm e f wf (z0v T z) *ᵥ zB' = z' := by
    rw [hzB', Matrix.mulVec_mulVec, Qm_mul_Qi hFJ, Matrix.one_mulVec]
  have hzB'W : inWb k r zB' := by
    intro i hi
    rcases hi with hi | hi
    · have hie : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hie, hzB', Qi_mulVec_eI, hfz']
    · exact Qi_perp z' hez' i hi
  have hTzB' : Tz k r zB' = T' := by
    have hw := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_P (gramQ hFJ) zB' zB'
    rw [hQzB', hzz'] at hw
    unfold Tz
    rw [← hw]
    simp
  have hHB : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf (z0v T z) *ᵥ zBv k r T)) μH := by
    rw [hQzB]; exact hH
  have hHB' : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf (z0v T z) *ᵥ zB')) μH' := by
    rw [hQzB']; exact hH'
  have hhB : IsSecLoc ε 1 e (Qm e f wf (z0v T z) *ᵥ zBv k r T) (Qm e f wf (z0v T z) *ᵥ zB')
      (Tz k r (zBv k r T)) (Tz k r zB') h := by
    rw [hQzB, hQzB', hTzB, hTzB']; exact hh
  have hD := jacLocX_of hJG k r ε e f wf (z0v T z) (zBv k r T) zB' hFJ hk hzB hzB'W (by rw [hTzB]; exact hT)
    (by rw [hTzB']; exact hT') hG μH μH' hHB hHB' a a' ha ha' hma hma' κ hκ h hhB
  rw [hTzB, hTzB'] at hD
  have hD2 := disint_smul_right (c := κ' / κ) (div_pos hκ' hκ) hD
  haveI : SigmaFinite μH' := hH'.1
  have hm : muSL μH' (ENNReal.ofReal κ' • refN ε e f wf (z0v T z)) =
      ENNReal.ofReal (κ' / κ) • muSL μH' (ENNReal.ofReal κ • refN ε e f wf (z0v T z)) := by
    rw [muSL_smul, muSL_smul, smul_smul, ← ENNReal.ofReal_mul (div_pos hκ' hκ).le, div_mul_cancel₀ _ hκ.ne']
  show DisintLoc ε k T T' (muSL μH (ENNReal.ofReal κ • refN ε e f wf (z0v T z)))
    (muSL μH' (ENNReal.ofReal κ' • refN ε e f wf (z0v T z))) h _
  rw [hm]
  convert hD2 using 1
  have hV1 := Jac.volU_pos (k - 1)
  field_simp

theorem refNg_isHaarLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool)
    (e f : Fin r → Fin n → ℂ) (wf : Fin k → Fin n → ℂ) (z z' : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (wf a) = 0) (hez' : ∀ a, hJ ε (e a) z' = 0) :
    IsHaarLoc (NLoc ε e z') (refNg hn ε e f wf (z0v T z)) := by
  subst hn
  have hs : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ * T = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hsC : ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt T)⁻¹ : ℝ)) : ℂ) * (T : ℂ) = 1 := by exact_mod_cast hs
  have hFJ : IsFrameJ ε e f wf (z0v T z) :=
    { ee := hee, ff := hff, ef := hef
      ez := fun a => by rw [z0v, JL.hJ_smul_r, hez, mul_zero]
      fz := fun a => by rw [z0v, JL.hJ_smul_r, hfz, mul_zero]
      zz := by
        rw [z0v, JL.hJ_smul_l, JL.hJ_smul_r, hzz, Complex.conj_ofReal]
        linear_combination (-1 : ℂ) * hsC
      ww := hww, ew := hew, fw := hfw
      zw := fun a => by rw [z0v, JL.hJ_smul_l, hzw, mul_zero] }
  have hQzB : Qm e f wf (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f wf (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQzB]; rfl⟩
  have h0 := refN_isHaarLoc hFJ (inWb_zB T) hz0
  rw [hQzB] at h0
  obtain ⟨h1, h2, h3, h4⟩ := h0
  have hNeq : NLoc ε e z' = NLoc ε e z := by
    ext g
    exact ⟨fun hg => inN_indep hez hg, fun hg => inN_indep hez' hg⟩
  show IsHaarLoc (NLoc ε e z') (refN ε e f wf (z0v T z))
  rw [hNeq]
  exact ⟨h1, h2, h3, h4⟩

end Formalism.L2.SG.Pf.NcReal.JX
