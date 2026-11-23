import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section gaugeCalc

variable (P : M.Par)

theorem ann_open : IsOpen (Ann P) := isOpen_lt continuous_const Complex.continuous_normSq

theorem ev_inv' (f : SmQ P.r P.TT) (hf : IsUnit f) (q : Qp P.r P.TT) :
    ((Ring.inverse f : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = ((f : Qp P.r P.TT → ℂ) q)⁻¹ := by
  obtain ⟨u, rfl⟩ := hf
  rw [Ring.inverse_unit]
  have h := congrArg (fun g : SmQ P.r P.TT => (g : Qp P.r P.TT → ℂ) q) u.mul_inv
  simp only [Subalgebra.coe_mul, Pi.mul_apply, OneMemClass.coe_one, Pi.one_apply] at h
  exact eq_inv_of_mul_eq_one_right h

theorem smZ {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) :
    (fun q : Qp P.r P.TT => v q.1.2) ∈ smSub P.r P.TT := by
  show ContDiffOn ℝ MA.sm (MA.ext (fun q : MA.Qp P.r P.TT => v q.1.2)) (MA.Qset P.r P.TT)
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MA.E P.r => v x.2) (MA.Qset P.r P.TT) :=
    hv.comp contDiff_snd.contDiffOn (fun x hx => show P.TT < Complex.normSq x.2 from hx.2)
  exact h1.congr (fun x hx => by simp [MA.ext, hx])

theorem fnZ_val {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) (q : Qp P.r P.TT) :
    ((fnZ P v : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = v q.1.2 := by
  have h := smZ P hv
  simp [fnZ, MA.toSm, h]

theorem coordQ_unit (hTT : 0 ≤ P.TT) (v : M.Var P.r) : IsUnit (coordQ v : SmQ P.r P.TT) := by
  have hne : ∀ x ∈ MA.Qset P.r P.TT, MA.coordE v x ≠ 0 := by
    intro x hx
    have hz : MA.zE v x ≠ 0 := by
      unfold MA.zE
      split_ifs with h
      · exact hx.1 _
      · intro h0
        have h1 : P.TT < Complex.normSq x.2 := hx.2
        rw [h0, Complex.normSq_zero] at h1
        linarith
    unfold MA.coordE
    split_ifs
    · exact hz
    · exact (map_ne_zero _).mpr hz
  have hmem : (fun q : MA.Qp P.r P.TT => (MA.coordE v q.1)⁻¹) ∈ MA.smSub P.r P.TT := by
    show ContDiffOn ℝ MA.sm (MA.ext (fun q : MA.Qp P.r P.TT => (MA.coordE v q.1)⁻¹)) (MA.Qset P.r P.TT)
    have h1 : ContDiffOn ℝ MA.sm (fun x => (MA.coordE v x)⁻¹) (MA.Qset P.r P.TT) :=
      (MA.coordE_smooth v).contDiffOn.inv hne
    exact h1.congr (fun x hx => by simp [MA.ext, hx])
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  funext q
  show MA.coordE v q.1 * (MA.coordE v q.1)⁻¹ = 1
  exact mul_inv_cancel₀ (hne q.1 q.2)

theorem dzQ_apply (hTT : 0 ≤ P.TT) (f : SmQ P.r P.TT) (q : Qp P.r P.TT) :
    ((dzQ P f : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = wirt M.vz (MA.ext (f : Qp P.r P.TT → ℂ)) q.1 := by
  show ((Ring.inverse (coordQ M.vz : SmQ P.r P.TT) : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q *
      (MA.coordE M.vz q.1 * wirt M.vz (MA.ext (f : Qp P.r P.TT → ℂ)) q.1) = _
  rw [ev_inv' P _ (coordQ_unit P hTT M.vz) q]
  have hz : q.1.2 ≠ 0 := by
    intro h0
    have h2 := q.2.2
    rw [h0, Complex.normSq_zero] at h2
    linarith
  have hne : MA.coordE M.vz q.1 ≠ 0 := by
    have h1 : MA.coordE M.vz q.1 = q.1.2 := by
      simp [MA.coordE, MA.zE, M.vz]
    rw [h1]
    exact hz
  rw [show ((coordQ M.vz : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = MA.coordE M.vz q.1 from rfl,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem dzbQ_apply (hTT : 0 ≤ P.TT) (f : SmQ P.r P.TT) (q : Qp P.r P.TT) :
    ((dzbQ P f : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = wirt M.vzb (MA.ext (f : Qp P.r P.TT → ℂ)) q.1 := by
  show ((Ring.inverse (coordQ M.vzb : SmQ P.r P.TT) : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q *
      (MA.coordE M.vzb q.1 * wirt M.vzb (MA.ext (f : Qp P.r P.TT → ℂ)) q.1) = _
  rw [ev_inv' P _ (coordQ_unit P hTT M.vzb) q]
  have hz : q.1.2 ≠ 0 := by
    intro h0
    have h2 := q.2.2
    rw [h0, Complex.normSq_zero] at h2
    linarith
  have hne : MA.coordE M.vzb q.1 ≠ 0 := by
    have h1 : MA.coordE M.vzb q.1 = (starRingEnd ℂ) q.1.2 := by
      simp [MA.coordE, MA.zE, M.vzb]
    rw [h1]
    exact (map_ne_zero _).mpr hz
  rw [show ((coordQ M.vzb : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q = MA.coordE M.vzb q.1 from rfl,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem wirtQ_mul (v : M.Var P.r) (f g : SmQ P.r P.TT) (q : Qp P.r P.TT) :
    wirt v (MA.ext ((f * g : SmQ P.r P.TT) : Qp P.r P.TT → ℂ)) q.1 =
      wirt v (MA.ext (f : Qp P.r P.TT → ℂ)) q.1 * (g : Qp P.r P.TT → ℂ) q +
        (f : Qp P.r P.TT → ℂ) q * wirt v (MA.ext (g : Qp P.r P.TT → ℂ)) q.1 := by
  have h1o : IsOpen {x : MA.E P.r | ∀ l, x.1 l ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite
      (fun l => isOpen_ne_fun ((continuous_apply l).comp continuous_fst) continuous_const)
  have hopen : IsOpen (MA.Qset P.r P.TT) :=
    h1o.inter (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))
  have heq : MA.ext ((f * g : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) =ᶠ[nhds q.1]
      (fun x => MA.ext (f : Qp P.r P.TT → ℂ) x * MA.ext (g : Qp P.r P.TT → ℂ) x) := by
    filter_upwards [hopen.mem_nhds q.2] with x hx
    simp [MA.ext, hx]
  have hf := MA.ext_smooth_diff f.2 q.1 q.2
  have hg := MA.ext_smooth_diff g.2 q.1 q.2
  have hD : fderiv ℝ (MA.ext ((f * g : SmQ P.r P.TT) : Qp P.r P.TT → ℂ)) q.1 =
      MA.ext (f : Qp P.r P.TT → ℂ) q.1 • fderiv ℝ (MA.ext (g : Qp P.r P.TT → ℂ)) q.1 +
        MA.ext (g : Qp P.r P.TT → ℂ) q.1 • fderiv ℝ (MA.ext (f : Qp P.r P.TT → ℂ)) q.1 :=
    heq.fderiv_eq.trans (fderiv_mul hf hg)
  have hfq : MA.ext (f : Qp P.r P.TT → ℂ) q.1 = (f : Qp P.r P.TT → ℂ) q := by simp [MA.ext, q.2]
  have hgq : MA.ext (g : Qp P.r P.TT → ℂ) q.1 = (g : Qp P.r P.TT → ℂ) q := by simp [MA.ext, q.2]
  unfold MA.wirt
  rw [hD]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hfq, hgq]
  ring

theorem fnZ_ev_eq {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) (q : Qp P.r P.TT) :
    MA.ext ((fnZ P v : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] (fun x : E P.r => v x.2) := by
  have h1 : IsOpen {x : MA.E P.r | ∀ l, x.1 l ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite
      (fun l => isOpen_ne_fun ((continuous_apply l).comp continuous_fst) continuous_const)
  have hopen : IsOpen (MA.Qset P.r P.TT) :=
    h1.inter (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))
  filter_upwards [hopen.mem_nhds q.2] with x hx
  simp only [MA.ext, dif_pos hx]
  exact fnZ_val P hv ⟨x, hx⟩

theorem fderiv_snd_comp {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) (q : Qp P.r P.TT) :
    fderiv ℝ (fun x : E P.r => v x.2) q.1 = (fderiv ℝ v q.1.2).comp (ContinuousLinearMap.snd ℝ _ _) := by
  have hq : q.1.2 ∈ Ann P := q.2.2
  have hd : DifferentiableAt ℝ v q.1.2 :=
    (hv.differentiableOn (by first | simp | exact_mod_cast le_top)).differentiableAt
      ((ann_open P).mem_nhds hq)
  rw [show (fun x : E P.r => v x.2) = v ∘ Prod.snd from rfl, fderiv_comp q.1 hd differentiableAt_snd,
    fderiv_snd]

theorem wirtinger_derivative_fibre_function {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) (q : Qp P.r P.TT) :
    wirt M.vz (MA.ext ((fnZ P v : SmQ P.r P.TT) : Qp P.r P.TT → ℂ)) q.1 = NF.dZ v q.1.2 := by
  have h1 : fderiv ℝ (MA.ext ((fnZ P v : SmQ P.r P.TT) : Qp P.r P.TT → ℂ)) q.1 =
      (fderiv ℝ v q.1.2).comp (ContinuousLinearMap.snd ℝ _ _) :=
    (fnZ_ev_eq P hv q).fderiv_eq.trans (fderiv_snd_comp P hv q)
  unfold MA.wirt
  rw [h1]
  simp [MA.dirE, M.vz, NF.dZ] <;> ring

theorem wirt_fnZ_zb {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) (q : Qp P.r P.TT) :
    wirt M.vzb (MA.ext ((fnZ P v : SmQ P.r P.TT) : Qp P.r P.TT → ℂ)) q.1 = NF.dZb v q.1.2 := by
  have h1 : fderiv ℝ (MA.ext ((fnZ P v : SmQ P.r P.TT) : Qp P.r P.TT → ℂ)) q.1 =
      (fderiv ℝ v q.1.2).comp (ContinuousLinearMap.snd ℝ _ _) :=
    (fnZ_ev_eq P hv q).fderiv_eq.trans (fderiv_snd_comp P hv q)
  unfold MA.wirt
  rw [h1]
  simp [MA.dirE, M.vzb, NF.dZb] <;> ring

private theorem star_mul_self_eq_one_of_norm_eq_one {z : ℂ} (h : ‖z‖ = 1) : star z * z = 1 := by
  calc star z * z = (starRingEnd ℂ) z * z := rfl
    _ = ((‖z‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
    _ = 1 := by rw [h]; norm_num

theorem dZ_conj_unit {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (Ann P))
    (h1 : ∀ ζ ∈ Ann P, ‖u ζ‖ = 1) {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    NF.dZ (fun w => star (u w)) ζ = -(star (u ζ)) ^ 2 * NF.dZ u ζ ∧
      NF.dZb (fun w => star (u w)) ζ = -(star (u ζ)) ^ 2 * NF.dZb u ζ := by
  have hd : DifferentiableAt ℝ u ζ :=
    (hu.differentiableOn (by first | simp | exact_mod_cast le_top)).differentiableAt
      ((ann_open P).mem_nhds hζ)
  have hstar : ∀ h : ℂ, fderiv ℝ (fun w => star (u w)) ζ h = star (fderiv ℝ u ζ h) := by
    intro h
    first
    | (rw [fderiv_star]; rfl)
    | (rw [(hd.hasFDerivAt.star).fderiv]; rfl)
  have hconst : (fun w => u w * star (u w)) =ᶠ[nhds ζ] fun _ => (1 : ℂ) := by
    filter_upwards [(ann_open P).mem_nhds hζ] with w hw
    rw [mul_comm]
    exact star_mul_self_eq_one_of_norm_eq_one (h1 w hw)
  have hD : ∀ h : ℂ, u ζ * star (fderiv ℝ u ζ h) + star (u ζ) * fderiv ℝ u ζ h = 0 := by
    intro h
    have h2 := congrArg (fun L : ℂ →L[ℝ] ℂ => L h)
      ((fderiv_mul hd hd.star).symm.trans (hconst.fderiv_eq.trans (fderiv_const_apply _)))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.zero_apply] at h2
    rw [hstar] at h2
    exact h2
  have hN : star (u ζ) * u ζ = 1 := star_mul_self_eq_one_of_norm_eq_one (h1 ζ hζ)
  have hc : ∀ h : ℂ, star (fderiv ℝ u ζ h) = -(star (u ζ)) ^ 2 * fderiv ℝ u ζ h := by
    intro h
    linear_combination (star (u ζ)) * hD h - star (fderiv ℝ u ζ h) * hN
  constructor
  · simp only [NF.dZ]
    rw [hstar, hstar, hc, hc]
    ring
  · simp only [NF.dZb]
    rw [hstar, hstar, hc, hc]
    ring

theorem mul_conjCoordinate_apply (f : SmQ P.r P.TT) (q : Qp P.r P.TT) :
    ((show SmQ P.r P.TT from ((MA.DQ P).zbP).1 f) : Qp P.r P.TT → ℂ) q = star q.1.2 * (f : Qp P.r P.TT → ℂ) q := by
  show MA.coordE M.vzb q.1 * (f : Qp P.r P.TT → ℂ) q = star q.1.2 * (f : Qp P.r P.TT → ℂ) q
  congr 1
  first
  | (simp [MA.coordE, MA.zE, M.vzb]; done)
  | (simp [MA.coordE, MA.zE, M.vzb]; rfl)

theorem algebraMap_comp_ofPadicInt_apply (f : SmQ P.r P.TT) (q : Qp P.r P.TT) :
    ((show SmQ P.r P.TT from ((MA.DQ P).zP).1 f) : Qp P.r P.TT → ℂ) q = q.1.2 * (f : Qp P.r P.TT → ℂ) q := by
  show MA.coordE M.vz q.1 * (f : Qp P.r P.TT → ℂ) q = q.1.2 * (f : Qp P.r P.TT → ℂ) q
  congr 1
  simp [MA.coordE, MA.zE, M.vz]

theorem ggiP_apply (f : SmQ P.r P.TT) (q : Qp P.r P.TT) :
    ((show SmQ P.r P.TT from ((MA.DQ P).ggiP P.TT).1 f) : Qp P.r P.TT → ℂ) q =
      ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * (f : Qp P.r P.TT → ℂ) q := by
  have hsq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ζ : ℂ => ((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹) (Ann P) := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
      first
      | exact contDiff_id.star
      | exact Complex.conjCLE.contDiff
      | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
    have h : (fun ζ : ℂ => ((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹) =
        fun ζ : ℂ => (ζ * star ζ - (P.TT : ℂ))⁻¹ := by
      funext ζ
      rw [← Complex.mul_conj]
      rfl
    rw [h]
    apply ContDiffOn.inv
    · exact ((contDiff_id.mul hs).sub contDiff_const).contDiffOn
    · intro ζ hζ
      rw [show ζ * star ζ = ((Complex.normSq ζ : ℝ) : ℂ) from Complex.mul_conj ζ, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hζ).ne'
  have hval : ∀ q' : Qp P.r P.TT, ((show SmQ P.r P.TT from (MA.DQ P).gg P.TT) : Qp P.r P.TT → ℂ) q' =
      (Complex.normSq q'.1.2 : ℂ) - (P.TT : ℂ) := by
    intro q'
    have e1 : MA.coordE M.vz q'.1 = q'.1.2 := by simp [MA.coordE, MA.zE, M.vz]
    have e2 : MA.coordE M.vzb q'.1 = (starRingEnd ℂ) q'.1.2 := by simp [MA.coordE, MA.zE, M.vzb]
    show MA.coordE M.vz q'.1 * MA.coordE M.vzb q'.1 - (P.TT : ℂ) = _
    rw [e1, e2, Complex.mul_conj]
  have hne : ∀ q' : Qp P.r P.TT, (Complex.normSq q'.1.2 : ℂ) - (P.TT : ℂ) ≠ 0 := by
    intro q'
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr q'.2.2).ne'
  have hu : IsUnit (show SmQ P.r P.TT from (MA.DQ P).gg P.TT) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, smZ P hsq⟩, ?_⟩
    apply Subtype.ext
    funext q'
    show ((show SmQ P.r P.TT from (MA.DQ P).gg P.TT) : Qp P.r P.TT → ℂ) q' *
      ((Complex.normSq q'.1.2 : ℂ) - (P.TT : ℂ))⁻¹ = 1
    rw [hval q']
    exact mul_inv_cancel₀ (hne q')
  show ((Ring.inverse (show SmQ P.r P.TT from (MA.DQ P).gg P.TT) : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q * (f : Qp P.r P.TT → ℂ) q = _
  rw [ev_inv' P _ hu q, hval q]

end gaugeCalc

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
