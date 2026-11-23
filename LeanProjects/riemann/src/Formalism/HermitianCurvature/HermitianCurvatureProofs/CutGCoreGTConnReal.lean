import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSAdjH
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRadAdj

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSReal

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem dZb_eq (f : ℂ → ℂ) (ζ : ℂ) :
    NF.dZb f ζ = (1 / 2 : ℂ) * fderiv ℝ f ζ 1 + (1 / 2 * Complex.I) * fderiv ℝ f ζ Complex.I := by
  unfold NF.dZb; ring

theorem ibp_dZb (f g : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∫ ζ, f ζ * NF.dZb g ζ = -∫ ζ, NF.dZb f ζ * g ζ := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have cf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have cg : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hgc' : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  have I1 : ∀ v : ℂ, Integrable (fun x => fderiv ℝ f x v * g x) := fun v =>
    ((cf.clm_apply continuous_const).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have I2 : ∀ v : ℂ, Integrable (fun x => f x * fderiv ℝ g x v) := fun v => by
    refine (hf.continuous.mul (cg.clm_apply continuous_const)).integrable_of_hasCompactSupport ?_
    exact (hgc.fderiv_apply (𝕜 := ℝ) v).mul_left
  have I3 : Integrable (fun x => f x * g x) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have e1 : ∫ x, f x * fderiv ℝ g x 1 = -∫ x, fderiv ℝ f x 1 * g x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (I1 1) (I2 1) I3
      (fun x _ => hfd x) (fun x _ => hgd x)
  have e2 : ∫ x, f x * fderiv ℝ g x Complex.I = -∫ x, fderiv ℝ f x Complex.I * g x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (I1 _) (I2 _) I3
      (fun x _ => hfd x) (fun x _ => hgd x)
  simp only [dZb_eq]
  have L : ∫ ζ, f ζ * ((1 / 2 : ℂ) * fderiv ℝ g ζ 1 + (1 / 2 * Complex.I) * fderiv ℝ g ζ Complex.I) =
      (1 / 2 : ℂ) * (∫ ζ, f ζ * fderiv ℝ g ζ 1) + (1 / 2 * Complex.I) * (∫ ζ, f ζ * fderiv ℝ g ζ Complex.I) := by
    have h := integral_add ((I2 1).const_mul (1 / 2 : ℂ)) ((I2 Complex.I).const_mul (1 / 2 * Complex.I))
    rw [integral_const_mul, integral_const_mul] at h
    rw [← h]
    congr 1; funext ζ; ring
  have R : ∫ ζ, ((1 / 2 : ℂ) * fderiv ℝ f ζ 1 + (1 / 2 * Complex.I) * fderiv ℝ f ζ Complex.I) * g ζ =
      (1 / 2 : ℂ) * (∫ ζ, fderiv ℝ f ζ 1 * g ζ) + (1 / 2 * Complex.I) * (∫ ζ, fderiv ℝ f ζ Complex.I * g ζ) := by
    have h := integral_add ((I1 1).const_mul (1 / 2 : ℂ)) ((I1 Complex.I).const_mul (1 / 2 * Complex.I))
    rw [integral_const_mul, integral_const_mul] at h
    rw [← h]
    congr 1; funext ζ; ring
  rw [L, R]
  linear_combination (1 / 2 : ℂ) * e1 + (1 / 2 * Complex.I) * e2

theorem dZb_conj (F : ℂ → ℂ) (ζ : ℂ) (hF : DifferentiableAt ℝ F ζ) :
    NF.dZb (fun w => star (F w)) ζ = star (NF.dZ F ζ) := by
  have h : HasFDerivAt (fun w => star (F w))
      ((Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).comp (fderiv ℝ F ζ)) ζ :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp ζ hF.hasFDerivAt
  unfold NF.dZb NF.dZ
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  simp only [star_mul', star_sub, Complex.star_def, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

theorem dZb_mul_gg (G : ℂ → ℂ) (TT : ℝ) (ζ : ℂ) (hG : DifferentiableAt ℝ G ζ) :
    NF.dZb (fun w => G w * ((Complex.normSq w : ℂ) - (TT : ℂ))) ζ =
      NF.dZb G ζ * ((Complex.normSq ζ : ℂ) - (TT : ℂ)) + G ζ * ζ := by
  have hn : ∀ w : ℂ, ((Complex.normSq w : ℂ) - (TT : ℂ)) = w * star w - (TT : ℂ) := by
    intro w; rw [Complex.star_def, Complex.mul_conj]
  simp_rw [hn]
  have hc : HasFDerivAt (fun w : ℂ => star w) (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) ζ :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  have hid : HasFDerivAt (fun w : ℂ => w) (ContinuousLinearMap.id ℝ ℂ) ζ := hasFDerivAt_id ζ
  have hp := (hid.mul hc).sub_const (TT : ℂ)
  have hq : HasFDerivAt (fun w => G w * (w * star w - (TT : ℂ)))
      (G ζ • (ζ • (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) + star ζ • ContinuousLinearMap.id ℝ ℂ) +
        (ζ * star ζ - (TT : ℂ)) • fderiv ℝ G ζ) ζ := hG.hasFDerivAt.mul hp
  unfold NF.dZb
  rw [hq.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul, Complex.star_def, map_one, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

section vals

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem rawR_sub (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Z W : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P μsec e (Z - W) ρ q = rawR P μsec e Z ρ q - rawR P μsec e W ρ q := by
  unfold rawR
  simp only [Pi.sub_apply]
  rw [SSC.hsVec_sub, inner_sub_right, mul_sub]

theorem rawR_neg [FiniteDimensional ℂ Wp] (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P μsec e (-Z) ρ q = -rawR P μsec e Z ρ q := by
  have h := rawR_sub P μsec e 0 Z ρ q
  rw [zero_sub, SSAdjH.rawR_zero, zero_sub] at h
  exact h

section gg
open Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.P.MAx1.An

theorem ggP_val (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((show MA.SmQ P.r P.TT from ((MA.DQ P).ggP P.TT).1 f) : MA.Qp P.r P.TT → ℂ) q =
      ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ)) * (f : MA.Qp P.r P.TT → ℂ) q := by
  show ((ggQ P.r P.TT : SmQ P.r P.TT) : Qp P.r P.TT → ℂ) q * (f : Qp P.r P.TT → ℂ) q = _
  rw [gg_apply, coordE_vz, coordE_vzb, Complex.mul_conj]

end gg

end vals

section atoms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
  (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hH : GTHyp P Bs X d)
  (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)

include hH he

theorem v_fn (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e ((d.L.ζb.1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
        star q.1.2 * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q ∧
    rawR P Bs.μsec e ((d.L.ζ.1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
        q.1.2 * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q ∧
    rawR P Bs.μsec e ((d.L.GGi.1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
        ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q ∧
    rawR P Bs.μsec e ((d.L.GG.1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
        ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ)) * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
  have hpl := hH.1
  have hk2 := hH.2.1
  have hv := SSC.vl_fn P Bs X d hH e Z ρ q
  simp only [SSC.vl, SSTr.trR_apply P Bs hpl hk2 e he] at hv
  obtain ⟨f1, f2, f3⟩ := hv
  refine ⟨f2, f1, f3, ?_⟩
  obtain ⟨-, -, -, -, f5, -⟩ := GT.gauge_function_holds Wp Wq P Bs X d hH e Z
  rw [← SSTr.trR_apply P Bs hpl hk2 e he, ← SSTr.trR_apply P Bs hpl hk2 e he,
    show trR P Bs e (d.L.GG.1 Z) ρ = _ from congrFun f5 ρ]
  exact (congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) q) (SSC.actA_sc P _ _ ρ)).trans
    (ggP_val P _ q)

theorem v_conn (A Bf : M.Ty P → ℂ → ℂ) (hAB : SmAB P A Bf) (hC : ConnF P Bs d e A Bf)
    (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (F : ℂ → ℂ)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Ann P))
    (hZ : ∀ q : MA.Qp P.r P.TT, rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = F q.1.2)
    (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e ((d.L.nab.1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
        NF.dZ F q.1.2 + A ρ q.1.2 * F q.1.2 ∧
    rawR P Bs.μsec e ((d.L.nabs.1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
        -NF.dZb F q.1.2 + Bf ρ q.1.2 * F q.1.2 := by
  have hpl := hH.1
  have hk2 := hH.2.1
  have hTT : 0 ≤ P.TT := (mul_pos hpl.1.T_pos hpl.1.T'_pos).le
  have htr : trR P Bs e Z ρ = fnZ P F := by
    apply Subtype.ext
    funext q'
    rw [SSTr.trR_apply P Bs hpl hk2 e he, hZ q', fnZ_val P hF q']
  refine ⟨?_, ?_⟩
  · rw [← SSTr.trR_apply P Bs hpl hk2 e he, (hC Z ρ).1, htr]
    show ((dzQ P (fnZ P F) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q +
      ((fnZ P (A ρ) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q * ((fnZ P F : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = _
    rw [dzQ_apply P hTT, wirtinger_derivative_fibre_function P hF q, fnZ_val P (hAB ρ).1 q, fnZ_val P hF q]
  · rw [← SSTr.trR_apply P Bs hpl hk2 e he, (hC Z ρ).2, htr]
    show -((dzbQ P (fnZ P F) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q +
      ((fnZ P (Bf ρ) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q * ((fnZ P F : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = _
    rw [dzbQ_apply P hTT, wirt_fnZ_zb P hF q, fnZ_val P (hAB ρ).2 q, fnZ_val P hF q]

theorem v_pj (hk : KapF P Bs d e) (W : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e (((Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 W : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
      rawR P Bs.μsec e (W : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
  have h := SSAdjH.kap_pt P Bs hH.1 hH.2.1 e he d hk (fun σ => if σ = ρ then (1 : ℂ) else 0) W ρ q
  simp only [if_true, one_mul] at h
  exact h

theorem blk (hk : KapF P Bs d e) (A Bf : M.Ty P → ℂ → ℂ) (hAB : SmAB P A Bf) (hC : ConnF P Bs d e A Bf)
    (ρ : M.Ty P) (Y : ℂ) (F : ℂ → ℂ) (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Ann P))
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (hΦr : ∀ σ (q : MA.Qp P.r P.TT), rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
      (if σ = ρ then 1 else 0) * F q.1.2) (hΦP : (Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 Φ = Φ) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e ((X.t Y 1 0 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
        M.xC P ρ Y * (-(((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ)) * (NF.dZ F q.1.2 + A ρ q.1.2 * F q.1.2)) -
          (Y + 1 / 2) * (star q.1.2 * F q.1.2)) ∧
    rawR P Bs.μsec e ((X.t Y 0 1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q =
        M.xC P ρ Y * (-(((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ)) * (-NF.dZb F q.1.2 + Bf ρ q.1.2 * F q.1.2)) -
          (Y - 1 / 2) * (q.1.2 * F q.1.2)) := by
  have hRel := hH.2.2.2.2.2.1
  have hQ := hH.2.2.2.2.2.2
  have hΦρ : ∀ q : MA.Qp P.r P.TT, rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = F q.1.2 := by
    intro q'; rw [hΦr ρ q', if_pos rfl, one_mul]
  have hgg : ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ)) ≠ 0 := by
    have h2 := q.2.2
    intro h0
    have h3 : ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have h4 : Complex.normSq q.1.2 - P.TT = 0 := by exact_mod_cast h3
    linarith
  obtain ⟨nb, nbs⟩ := v_conn P Bs X d hH e he A Bf hAB hC Φ ρ F hF hΦρ q
  constructor
  · have hB := congrArg (fun p : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => p.1 Φ) (Formalism.FourierDecayAlt.P.NFx4.NO.B3 hRel Y ρ)
    have L : (Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ * d.QQ Y 1 0 * Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 Φ = (Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 (X.t Y 1 0 Φ) := by
      show (Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 ((d.QQ Y 1 0).1 ((Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 Φ)) = _
      rw [hΦP, ← hQ Y]; rfl
    have R : (M.xC P ρ Y • (d.L.GG * d.L.l0 Y * Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ)).1 Φ =
        M.xC P ρ Y • d.L.GG.1 (-(d.L.nab.1 Φ) - (Y + 1 / 2) • d.L.ζb.1 (d.L.GGi.1 Φ)) := by
      rw [Algebra.smul_def]
      show (algebraMap ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (M.xC P ρ Y)).1
        (d.L.GG.1 ((d.L.l0 Y).1 ((Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 Φ))) = _
      rw [hΦP]; rfl
    rw [L, R] at hB
    have hv := congrArg (fun Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' =>
      rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q) hB
    try simp only at hv
    rw [v_pj P Bs X d hH e he hk] at hv
    rw [hv, Submodule.coe_smul, SSAdjH.rawR_smul, (v_fn P Bs X d hH e he _ ρ q).2.2.2, Submodule.coe_sub,
      rawR_sub, Submodule.coe_neg, rawR_neg, Submodule.coe_smul, SSAdjH.rawR_smul, nb,
      (v_fn P Bs X d hH e he _ ρ q).1, (v_fn P Bs X d hH e he _ ρ q).2.2.1, hΦρ q]
    field_simp
  · have hB := congrArg (fun p : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => p.1 Φ) (Formalism.FourierDecayAlt.P.NFx4.NO.B5 hRel Y ρ)
    have L : (Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ * d.QQ Y 0 1 * Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 Φ = (Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 (X.t Y 0 1 Φ) := by
      show (Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 ((d.QQ Y 0 1).1 ((Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 Φ)) = _
      rw [hΦP, ← hQ Y]; rfl
    have R : (M.xC P ρ Y • (d.L.GG * d.L.m0 Y * Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ)).1 Φ =
        M.xC P ρ Y • d.L.GG.1 (-(d.L.nabs.1 Φ) - (Y - 1 / 2) • d.L.ζ.1 (d.L.GGi.1 Φ)) := by
      rw [Algebra.smul_def]
      show (algebraMap ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (M.xC P ρ Y)).1
        (d.L.GG.1 ((d.L.m0 Y).1 ((Formalism.FourierDecayAlt.P.NFx4.NO.Pj d ρ).1 Φ))) = _
      rw [hΦP]; rfl
    rw [L, R] at hB
    have hv := congrArg (fun Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' =>
      rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q) hB
    try simp only at hv
    rw [v_pj P Bs X d hH e he hk] at hv
    rw [hv, Submodule.coe_smul, SSAdjH.rawR_smul, (v_fn P Bs X d hH e he _ ρ q).2.2.2, Submodule.coe_sub,
      rawR_sub, Submodule.coe_neg, rawR_neg, Submodule.coe_smul, SSAdjH.rawR_smul, nbs,
      (v_fn P Bs X d hH e he _ ρ q).2.1, (v_fn P Bs X d hH e he _ ρ q).2.2.1, hΦρ q]
    field_simp

end atoms

theorem integ_of (P : M.Par) (f S : ℂ → ℂ) (hf : ContinuousOn f (Ann P)) (hS : HasCompactSupport S)
    (hSs : tsupport S ⊆ Ann P) (hfS : ∀ ζ, S ζ = 0 → f ζ = 0) : Integrable f := by
  have hsub : Function.support f ⊆ Function.support S := fun ζ h1 h2 => h1 (hfS ζ h2)
  have ht : tsupport f ⊆ tsupport S := closure_mono hsub
  have hc : Continuous f := hf.continuous_of_tsupport_subset (ann_open P) (ht.trans hSs)
  exact hc.integrable_of_hasCompactSupport (hS.mono hsub)

theorem dZ_cont {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) : Continuous (NF.dZ F) := by
  have c := hF.continuous_fderiv one_ne_zero
  unfold NF.dZ
  exact continuous_const.mul ((c.clm_apply continuous_const).sub
    (continuous_const.mul (c.clm_apply continuous_const)))

theorem dZb_cont {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) : Continuous (NF.dZb F) := by
  have c := hF.continuous_fderiv one_ne_zero
  unfold NF.dZb
  exact continuous_const.mul ((c.clm_apply continuous_const).add
    (continuous_const.mul (c.clm_apply continuous_const)))

set_option maxHeartbeats 4000000 in
theorem gauge_reality_holds : GTCReal := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk A Bf hAB hC ρ ζ0 hζ0
  classical
  have hpl := hH.1
  have hk2 := hH.2.1
  have hTT : 0 < P.TT := mul_pos hpl.1.T_pos hpl.1.T'_pos
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  let gg : ℂ → ℂ := fun ζ => (Complex.normSq ζ : ℂ) - (P.TT : ℂ)
  have gg_cont : Continuous gg :=
    (Complex.continuous_ofReal.comp Complex.continuous_normSq).sub continuous_const
  have gg_ne : ∀ ζ ∈ Ann P, gg ζ ≠ 0 := by
    intro ζ hζ h0
    have h2 : P.TT < Complex.normSq ζ := hζ
    have h3 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have h4 : Complex.normSq ζ - P.TT = 0 := by exact_mod_cast h3
    linarith
  have gg_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gg := by
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => Complex.normSq ζ) := by
      simp only [Complex.normSq_apply]
      exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
        (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
    exact (Complex.ofRealCLM.contDiff.comp this).sub contDiff_const

  let Yr : ℝ := 1 + ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P ρ i|
  have hxR : M.xC P ρ (Yr : ℂ) = ((∏ i ∈ Finset.Icc 1 (P.k - 1), (Yr + M.rho P ρ i) : ℝ) : ℂ) := by
    unfold M.xC; push_cast; rfl
  have hxne : M.xC P ρ (Yr : ℂ) ≠ 0 := by
    rw [hxR]
    have : (∏ i ∈ Finset.Icc 1 (P.k - 1), (Yr + M.rho P ρ i)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      have h1 : |M.rho P ρ i| ≤ ∑ j ∈ Finset.Icc 1 (P.k - 1), |M.rho P ρ j| :=
        Finset.single_le_sum (f := fun j => |M.rho P ρ j|) (fun j _ => abs_nonneg _) hi
      have h2 := neg_abs_le (M.rho P ρ i)
      have h3 : 0 < Yr + M.rho P ρ i := by simp only [Yr]; linarith
      exact h3.ne'
    exact_mod_cast this
  have hxr : (starRingEnd ℂ) (M.xC P ρ (Yr : ℂ)) = M.xC P ρ (Yr : ℂ) := by
    rw [hxR, Complex.conj_ofReal]
  set x := M.xC P ρ (Yr : ℂ) with hxdef

  have key : ∀ F G : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F → HasCompactSupport F → tsupport F ⊆ Ann P →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → HasCompactSupport G → tsupport G ⊆ Ann P →
      ∫ ζ, star (F ζ) * (gg ζ * (Bf ρ ζ - star (A ρ ζ))) * G ζ = 0 := by
    intro F G hF hFc hFs hG hGc hGs
    obtain ⟨Φ, hΦr, hΦP⟩ := SSAdjH.exists_proj P Bs hpl hk2 e he d hk F hF.contDiffOn ρ
    obtain ⟨Ψ, hΨr, hΨP⟩ := SSAdjH.exists_proj P Bs hpl hk2 e he d hk G hG.contDiffOn ρ
    have hvan : ∀ (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (H : ℂ → ℂ),
        (∀ σ (q : MA.Qp P.r P.TT), rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
          (if σ = ρ then 1 else 0) * H q.1.2) →
        ∀ ζ ∈ Ann P, ζ ∉ tsupport H → (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) = 0 := by
      intro Z H hZ ζ hζ hn
      have hs := SSAdjH.sec_expand P Bs hpl hk2 e he Z ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
      refine hs.trans (Finset.sum_eq_zero fun σ _ => ?_)
      rw [hZ, image_eq_zero_of_notMem_tsupport hn]
      simp
    have radj := radial_adjoint_identity_holds Wp Wq P Bs X d hH (Yr : ℂ) 1 0 c0 hc0 Φ Ψ
      ⟨tsupport F ∪ tsupport G, hFc.isCompact.union hGc.isCompact, Set.union_subset hFs hGs,
        fun ζ hζ hn => ⟨hvan Φ F hΦr ζ hζ (fun h => hn (Or.inl h)), hvan Ψ G hΨr ζ hζ (fun h => hn (Or.inr h))⟩⟩
    rw [show star (Yr : ℂ) = (Yr : ℂ) from Complex.conj_ofReal Yr] at radj

    have eL : Set.EqOn (fun ζ => (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
        inner ℂ (B.hsVec (((X.t (Yr : ℂ) 1 0 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
          c0 (NF.muZ P.k P.r Bs.μsec ζ))) (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ))))
        (fun ζ => star (x * (-(gg ζ * (NF.dZ F ζ + A ρ ζ * F ζ)) - ((Yr : ℂ) + 1 / 2) * (star ζ * F ζ))) * G ζ)
        (Ann P) := by
      intro ζ hζ
      let q : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
      have hp := SSAdjH.hs_pair P Bs hpl hk2 e he (X.t (Yr : ℂ) 1 0 Φ) Ψ q
      refine hp.trans ?_
      rw [Finset.sum_eq_single ρ]
      · rw [hΨr ρ q, if_pos rfl, one_mul, (blk P Bs X d hH e he hk A Bf hAB hC ρ (Yr : ℂ) F hF.contDiffOn Φ hΦr hΦP q).1]
      · intro σ _ hσ; rw [hΨr σ q, if_neg hσ, zero_mul, mul_zero]
      · intro h0; exact absurd (Finset.mem_univ _) h0
    have eR : Set.EqOn (fun ζ => (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
        inner ℂ (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ)))
          (B.hsVec (((X.t (Yr : ℂ) 0 1 Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
            c0 (NF.muZ P.k P.r Bs.μsec ζ))))
        (fun ζ => star (F ζ) * (x * (-(gg ζ * (-NF.dZb G ζ + Bf ρ ζ * G ζ)) - ((Yr : ℂ) - 1 / 2) * (ζ * G ζ))))
        (Ann P) := by
      intro ζ hζ
      let q : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
      have hp := SSAdjH.hs_pair P Bs hpl hk2 e he Φ (X.t (Yr : ℂ) 0 1 Ψ) q
      refine hp.trans ?_
      rw [Finset.sum_eq_single ρ]
      · rw [hΦr ρ q, if_pos rfl, one_mul, (blk P Bs X d hH e he hk A Bf hAB hC ρ (Yr : ℂ) G hG.contDiffOn Ψ hΨr hΨP q).2]
      · intro σ _ hσ; rw [hΦr σ q, if_neg hσ, zero_mul, star_zero, zero_mul]
      · intro h0; exact absurd (Finset.mem_univ _) h0
    rw [setIntegral_congr_fun (ann_open P).measurableSet eL, setIntegral_congr_fun (ann_open P).measurableSet eR]
      at radj
    have hGz : ∀ ζ, ζ ∉ Ann P → G ζ = 0 := fun ζ h => image_eq_zero_of_notMem_tsupport (fun h' => h (hGs h'))
    have hFz : ∀ ζ, ζ ∉ Ann P → F ζ = 0 := fun ζ h => image_eq_zero_of_notMem_tsupport (fun h' => h (hFs h'))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun ζ h => by rw [hGz ζ h, mul_zero]),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun ζ h => by rw [hFz ζ h, star_zero, zero_mul])]
      at radj
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast le_top)
    have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast le_top)
    have cF := hF.continuous
    have cG := hG.continuous
    have cdF := dZ_cont hF1
    have cdG := dZb_cont hG1
    have cA : ContinuousOn (A ρ) (Ann P) := (hAB ρ).1.continuousOn
    have cB : ContinuousOn (Bf ρ) (Ann P) := (hAB ρ).2.continuousOn
    let Lf : ℂ → ℂ := fun ζ => star (x * (-(gg ζ * (NF.dZ F ζ + A ρ ζ * F ζ)) - ((Yr : ℂ) + 1 / 2) * (star ζ * F ζ))) * G ζ
    let Rf : ℂ → ℂ := fun ζ => star (F ζ) * (x * (-(gg ζ * (-NF.dZb G ζ + Bf ρ ζ * G ζ)) - ((Yr : ℂ) - 1 / 2) * (ζ * G ζ)))
    let Ja : ℂ → ℂ := fun ζ => G ζ * gg ζ * star (NF.dZ F ζ)
    let Jb : ℂ → ℂ := fun ζ => (NF.dZb G ζ * gg ζ + G ζ * ζ) * star (F ζ)
    let Kf : ℂ → ℂ := fun ζ => star (F ζ) * (gg ζ * (Bf ρ ζ - star (A ρ ζ))) * G ζ
    have iL : Integrable Lf := integ_of P Lf G (by
        simp only [Lf]
        exact (continuous_star.comp_continuousOn (continuousOn_const.mul
          ((((gg_cont.continuousOn.mul (cdF.continuousOn.add (cA.mul cF.continuousOn)))).neg).sub
            (continuousOn_const.mul (continuous_star.continuousOn.mul cF.continuousOn))))).mul cG.continuousOn)
      hGc hGs (fun ζ h => by simp only [Lf]; rw [h, mul_zero])
    have iR : Integrable Rf := integ_of P Rf F (by
        simp only [Rf]
        exact (continuous_star.comp_continuousOn cF.continuousOn).mul (continuousOn_const.mul
          ((gg_cont.continuousOn.mul ((cdG.continuousOn.neg).add (cB.mul cG.continuousOn))).neg.sub
            (continuousOn_const.mul (continuousOn_id.mul cG.continuousOn)))))
      hFc hFs (fun ζ h => by simp only [Rf]; rw [h, star_zero, zero_mul])
    have iJa : Integrable Ja := integ_of P Ja G (by
        simp only [Ja]
        exact ((cG.mul gg_cont).mul (continuous_star.comp cdF)).continuousOn)
      hGc hGs (fun ζ h => by simp only [Ja]; rw [h, zero_mul, zero_mul])
    have iJb : Integrable Jb := integ_of P Jb F (by
        simp only [Jb]
        exact (((cdG.mul gg_cont).add (cG.mul continuous_id)).mul (continuous_star.comp cF)).continuousOn)
      hFc hFs (fun ζ h => by simp only [Jb]; rw [h, star_zero, mul_zero])
    have iK : Integrable Kf := integ_of P Kf G (by
        simp only [Kf]
        exact ((continuous_star.comp_continuousOn cF.continuousOn).mul (gg_cont.continuousOn.mul
          (cB.sub (continuous_star.comp_continuousOn cA)))).mul cG.continuousOn)
      hGc hGs (fun ζ h => by simp only [Kf]; rw [h, mul_zero])
    have hpt : ∀ ζ, Lf ζ - Rf ζ = x * (-(Ja ζ + Jb ζ) + Kf ζ) := by
      intro ζ
      simp only [Lf, Rf, Ja, Jb, Kf, gg, Complex.star_def, map_mul, map_sub, map_neg, map_add, Complex.conj_ofReal,
        Complex.conj_conj, map_div₀, map_one, map_ofNat, hxr]
      ring
    have hibp := ibp_dZb (fun w => G w * gg w) (fun w => star (F w)) (hG1.mul (gg_sm.of_le (by exact_mod_cast le_top)))
      (Complex.conjCLE.contDiff.comp hF1) (hFc.comp_left (star_zero _))
    have eJa : (fun w => G w * gg w * NF.dZb (fun w => star (F w)) w) = Ja := by
      funext w; simp only [Ja]; rw [dZb_conj F w (hF1.differentiable one_ne_zero w)]
    have eJb : (fun w => NF.dZb (fun w => G w * gg w) w * star (F w)) = Jb := by
      funext w; simp only [Jb, gg]; rw [dZb_mul_gg G P.TT w (hG1.differentiable one_ne_zero w)]
    rw [eJa, eJb] at hibp
    have hsum : ∫ ζ, (Lf ζ - Rf ζ) = 0 := by rw [integral_sub iL iR, radj, sub_self]
    have h1 : (fun ζ => Lf ζ - Rf ζ) = fun ζ => ((-x) * Ja ζ + ((-x) * Jb ζ + x * Kf ζ)) := by
      funext ζ; rw [hpt]; ring
    rw [h1, integral_add (iJa.const_mul _)
        (show Integrable (fun ζ => (-x) * Jb ζ + x * Kf ζ) from (iJb.const_mul _).add (iK.const_mul _)),
      integral_add (iJb.const_mul _) (iK.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul,
      hibp] at hsum
    have h2 : x * (∫ ζ, Kf ζ) = 0 := by linear_combination hsum
    exact (mul_eq_zero.1 h2).resolve_left hxne

  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (ann_open P) ζ0 hζ0
  let χ : ContDiffBump ζ0 := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩
  let kk : ℂ → ℂ := fun ζ => gg ζ * (Bf ρ ζ - star (A ρ ζ))
  have ckk : ContinuousOn kk (Ann P) :=
    gg_cont.continuousOn.mul ((hAB ρ).2.continuousOn.sub (continuous_star.comp_continuousOn (hAB ρ).1.continuousOn))
  have hballA : Metric.ball ζ0 (ε / 3) ⊆ Ann P := (Metric.ball_subset_ball (by linarith)).trans hball
  have hχs : tsupport (fun ζ => ((χ ζ : ℝ) : ℂ)) ⊆ Ann P := by
    refine (tsupport_comp_subset Complex.ofReal_zero _).trans ?_
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by simp only [χ]; linarith)).trans hball
  have hH0 := SSAdjH.pt_of_tests (U := Metric.ball ζ0 (ε / 3)) Metric.isOpen_ball
    (H := fun ζ => ((χ ζ : ℝ) : ℂ) * kk ζ)
    ((Complex.continuous_ofReal.comp χ.continuous).continuousOn.mul (ckk.mono hballA))
    (fun φ hφ hφc hφs => by
      have := key (fun ζ => ((χ ζ : ℝ) : ℂ)) (fun ζ => ((φ ζ : ℝ) : ℂ))
        (Complex.ofRealCLM.contDiff.comp χ.contDiff) (χ.hasCompactSupport.comp_left Complex.ofReal_zero) hχs
        (Complex.ofRealCLM.contDiff.comp hφ) (hφc.comp_left Complex.ofReal_zero)
        ((tsupport_comp_subset Complex.ofReal_zero _).trans (hφs.trans hballA))
      rw [← this]
      congr 1
      funext ζ
      simp only [kk, Complex.real_smul, Complex.star_def, Complex.conj_ofReal]
      ring)
    ζ0 (Metric.mem_ball_self (by positivity))
  have h1 : χ ζ0 = 1 := χ.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
  simp only [h1, Complex.ofReal_one, one_mul, kk] at hH0
  have := (mul_eq_zero.1 hH0).resolve_left (gg_ne ζ0 hζ0)
  exact sub_eq_zero.1 this

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSReal

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gauge_reality_holds : GTCReal := SSReal.gauge_reality_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
