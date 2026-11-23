import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed

noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem good_eq {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) :
    Good X u u' = Set.univ.pi fun _ => GoodLoc (r := D.R.rS) (Tw u) (Tw u') := by
  ext y
  first
  | (simp only [Good, GoodLoc, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq])
  | (simp only [Good, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]; rfl)
  | (simp [Good, GoodLoc])
  | (show _ ↔ _; exact Iff.rfl)

theorem product_formula_holds : P5 := by
  intro hJac hDC hSM hU hNH hR D X u u' sc hsc
  have hep : ∀ v a b, hJ (X.B.I.ε v) (eV X v a) (pV X v b) = if a = b then 1 else 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
  have hpp : ∀ v a b, hJ (X.B.I.ε v) (pV X v a) (pV X v b) = 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ff]; simp)
  have hzp : ∀ w v b, hJ (X.B.I.ε v) (zV X w v) (pV X v b) = 0 := fun w v b => by
    have h0 : hJ (X.B.I.ε v) (pV X v b) (zV X w v) = 0 :=
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w b).2]; simp)
    rw [hJ_cj, h0, map_zero]
  have hSH : ∀ w v, IsHaarS (SLoc (X.B.I.ε v) (eV X v) (zV X w v)) (muSv X w v) := fun w v =>
    hNH _ _ _ _ _ _ _ _ _ _ (frameLoc_X X w u v) (hep v) (hpp v) (hzp w v) _ _ (muNv_haar X w v) (muHv_haar X w v)
  haveI : ∀ w v, SigmaFinite (muSv X w v) := fun w v => (hSH w v).1.1
  obtain ⟨κ, hκ0, hκT, hκ⟩ := muS_eq X u (fun v => inferInstance)
  obtain ⟨κ', hκ'0, hκ'T, hκ'⟩ := muS_eq X u' (fun v => inferInstance)
  have hsec := fun v => hSM _ _ _ _ _ _ _ _ _ sc (frameLoc_X X u u' v) hsc
  choose hs hsm hss using hsec
  have hjl := fun v => hJac _ _ _ _ _ _ _ _ _ sc (frameLoc_X X u u' v) hsc _ _ (hSH u v) (hSH u' v) (hs v) (hss v)
  choose Cv hCv hDis using hjl
  have hloc : ∀ v, Formalism.REAL.muG (X.B.I.ε v) =
      ((nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v)).prod ((muSv X u v).prod (muSv X u' v))).map
        (phiLoc (X.B.I.ε v) (hs v)) := fun v =>
    muG_eq_map _ _ _ _ _ _ _ (hsm v) _ (hDis v)
  set Cp : ℝ := ∏ v, Cv v with hCp
  have hCp0 : 0 < Cp := Finset.prod_pos fun v _ => hCv v
  have hκr : 0 < κ.toReal := ENNReal.toReal_pos hκ0 hκT
  have hκr' : 0 < κ'.toReal := ENNReal.toReal_pos hκ'0 hκ'T
  refine ⟨Cp / (κ.toReal * κ'.toReal), div_pos hCp0 (mul_pos hκr hκr'), fun φ hφ => ?_⟩
  have hpf := prod_formula (fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v))
    (muSv X u) (muSv X u') hs hsm hloc φ hφ
  change ∫⁻ x, φ x ∂(Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v)) = _
  rw [hpf]

  have hwm : ∀ v, Measurable fun c : Fin (D.R.rS + 1) → ℂ => ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') c) :=
    fun v => ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont D.R.k (Tw u) (Tw u')).measurable)
  have hν : Measure.pi (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v)) =
      ((dcInf X).restrict (Good X u u')).withDensity
        (fun c => ∏ v, ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') (c v))) := by
    unfold nuLoc
    haveI : SigmaFinite (dcLoc (r := D.R.rS)) := by unfold dcLoc; infer_instance
    rw [PiM.pi_withDensity _ _ hwm (fun v x => ENNReal.ofReal_ne_top), ← Measure.restrict_pi_pi, good_eq]
    rfl
  set H : (Cinf X) → X.B.I.Ginf := fun c v => hs v (c v) with hHd
  have hHm : Measurable H := measurable_pi_lambda _ fun v => (hsm v).comp (measurable_pi_apply v)
  set Fc : Cinf X → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * H c * s'⁻¹) ∂Measure.pi (muSv X u') ∂Measure.pi (muSv X u)
    with hFc
  have hFm : Measurable Fc := by
    have h1 : Measurable fun q : (Cinf X × X.B.I.Ginf) × X.B.I.Ginf => φ (q.1.2 * H q.1.1 * q.2⁻¹) :=
      hφ.comp (((measurable_snd.comp measurable_fst).mul (hHm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h1.lintegral_prod_right'.lintegral_prod_right'
  rw [show (∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => hs v (c v)) * s'⁻¹) ∂Measure.pi (muSv X u') ∂Measure.pi (muSv X u)
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v)) = ∫⁻ c, Fc c
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v) from rfl,
    hν, lintegral_withDensity_eq_lintegral_mul _
      (f := fun c : Cinf X => ∏ v, ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') (c v)))
      (Finset.measurable_prod _ fun v _ => (hwm v).comp (measurable_pi_apply v)) hFm]
  have hGm : MeasurableSet (Good X u u') := by
    rw [good_eq]; exact MeasurableSet.univ_pi fun v => measurableSet_goodLoc _ _
  refine setLIntegral_congr_fun hGm fun c hc => ?_
  simp only [Pi.mul_apply]
  have hcv : ∀ v, c v ∈ GoodLoc (r := D.R.rS) (Tw u) (Tw u') := fun v => by
    rw [good_eq, Set.mem_univ_pi] at hc; exact hc v

  have hW : ∏ v, ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') (c v)) = ENNReal.ofReal (Cp * wt X u u' c) := by
    rw [← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (hCv v).le (wtLoc_nonneg _ _ _ (hcv v)),
      Finset.prod_mul_distrib]
    rfl

  have hex := hR D X u u' sc hsc c hc
  have hh : HasDiag X u u' sc c (hOf X u u' sc c) := by
    unfold hOf; rw [dif_pos hex]; exact hex.choose_spec
  have hdc := fun v => hDC _ _ _ _ _ _ _ _ _ sc (frameLoc_X X u u' v) (c v) (hcv v) (hs v (c v)) (hOf X u u' sc c v)
    (hss v (c v) (hcv v)) (hh v)
  choose t ht t' ht' htt using hdc
  have hofe : hOf X u u' sc c = t * H c * t'⁻¹ := funext fun v => htt v
  have hrt : (Measure.pi (muSv X u)).map (fun x => x * t) = Measure.pi (muSv X u) :=
    PiM.pi_map_mul_right _ t fun v => hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u u' v) _ (hSH u v) (t v) (ht v)
  have hrt' : (Measure.pi (muSv X u')).map (fun x => x * t') = Measure.pi (muSv X u') :=
    PiM.pi_map_mul_right _ t' fun v => hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u' u v) _ (hSH u' v) (t' v) (ht' v)
  have hsw : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' sc c * s'⁻¹) ∂Measure.pi (muSv X u') ∂Measure.pi (muSv X u) = Fc c := by
    rw [hofe]; exact dc_switch _ _ φ hφ (H c) t t' hrt hrt'

  have hinner : ∀ s, Measurable fun s' : X.B.I.Ginf => φ (s * hOf X u u' sc c * s'⁻¹) := fun s =>
    hφ.comp (measurable_const.mul measurable_inv)
  have hG2 : Measurable fun s : X.B.I.Ginf => ∫⁻ s', φ (s * hOf X u u' sc c * s'⁻¹) ∂Measure.pi (muSv X u') :=
    (hφ.comp ((measurable_fst.mul measurable_const).mul measurable_snd.inv)).lintegral_prod_right'
  have hmu : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' sc c * s'⁻¹) ∂muS X u' ∂muS X u = κ * κ' * Fc c := by
    rw [hκ, hκ', lintegral_smul_measure]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_const_mul' _ _ hκ'T, hsw]
    ring
  have hwc : 0 ≤ wt X u u' c := by
    unfold wt
    exact Finset.prod_nonneg fun v _ => wtLoc_nonneg D.R.k _ _ (hcv v)
  have hk : κ * κ' = ENNReal.ofReal (κ.toReal * κ'.toReal) := by
    rw [ENNReal.ofReal_mul hκr.le, ENNReal.ofReal_toReal hκT, ENNReal.ofReal_toReal hκ'T]
  rw [hmu, hW, hk, ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (div_pos hCp0 (mul_pos hκr hκr')).le hwc)]
  congr 2
  field_simp

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
