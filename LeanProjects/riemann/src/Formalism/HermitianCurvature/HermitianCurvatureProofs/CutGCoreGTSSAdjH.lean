import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdjH

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.NFx4

noncomputable section

section pt

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_zero' : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec
  ext i
  simp

theorem rawR_smul (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (a : ℂ) (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P μsec e (a • Z) ρ q = a * rawR P μsec e Z ρ q := by
  have hs : ∀ A : Wq →L[ℂ] Wp, B.hsVec (a • A) = a • B.hsVec A := by
    intro A
    unfold B.hsVec
    ext i
    simp
  simp only [rawR, Pi.smul_apply, hs, inner_smul_right]
  ring

theorem rawR_zero (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P μsec e (0 : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = 0 := by
  simp only [rawR, Pi.zero_apply, hsVec_zero', inner_zero_right, mul_zero]

theorem smQ_sum_apply (P : M.Par) (x : M.Ty P → MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((∑ σ, x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = ∑ σ, ((x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
  simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]

variable (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk2 : 2 ≤ P.k)
  (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)

include hpl hk2 he

theorem kap_pt (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hk : KapF P Bs d e)
    (f : M.Ty P → ℂ) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e (((d.κ f).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
      f σ * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  have h := congrArg (fun x : M.Ty P → MA.SmQ P.r P.TT => ((x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) (hk f Z)
  simp only [actA_kap] at h
  rw [← SSTr.trR_apply P Bs hpl hk2 e he, h, ← SSTr.trR_apply P Bs hpl hk2 e he]
  rfl

theorem ss_pt (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ)
    (hst : SmST P s t) (hL : SSLoc P Bs d e s t) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e (((d.SS l).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q =
        ∑ σ, s l ρ' σ q.1.2 * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q ∧
      rawR P Bs.μsec e (((star (d.SS l)).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q =
        ∑ σ, t l ρ' σ q.1.2 * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  obtain ⟨h1, h2⟩ := hL l hl Z ρ'
  constructor
  · rw [← SSTr.trR_apply P Bs hpl hk2 e he, h1, smQ_sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P (hst l ρ' σ).1, SSTr.trR_apply P Bs hpl hk2 e he]
  · rw [← SSTr.trR_apply P Bs hpl hk2 e he, h2, smQ_sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P (hst l ρ' σ).2, SSTr.trR_apply P Bs hpl hk2 e he]

theorem sec_expand (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
      ∑ σ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) •
        e σ q.1.2 := by
  have hq : (q.1 : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := (SSTr.qr_iff P Bs hpl _).2 q.2
  have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (SSTr.radBase P Bs hpl)
    (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) Z.2
  have hF := hmem.2.1 _ hq
  simp only [NF.radR, Set.indicator_of_mem hq] at hF
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  obtain ⟨-, -, hexp⟩ := he.2 q.1.2 hζ
  conv_lhs => rw [hexp _ hF]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hw := SSTr.wR_pos P hζ
  simp only [rawR]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hw.ne', Complex.ofReal_one, one_mul]

theorem hs_pair (Z W : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    (((wR P.k P.TT q.1.2 ^ 2 : ℝ)) : ℂ) *
        inner ℂ (B.hsVec ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)))
          (B.hsVec ((W : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) =
      ∑ σ, star (rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) *
        rawR P Bs.μsec e (W : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  rw [sec_expand P Bs hpl hk2 e he W q, SSTr.hsVec_sum, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hw := (SSTr.wR_pos P (q.2.2 : P.TT < Complex.normSq q.1.2)).ne'
  rw [hsVec_smul, inner_smul_right]
  have hc : star (rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
        inner ℂ (B.hsVec ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) (B.hsVec (e σ q.1.2)) := by
    simp only [rawR]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, inner_conj_symm]
  rw [hc]
  have hw' : ((wR P.k P.TT q.1.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
  push_cast
  field_simp

theorem exists_proj (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hk : KapF P Bs d e)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ann P)) (ρ : M.Ty P) :
    ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∀ σ (q : MA.Qp P.r P.TT), rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
        (if σ = ρ then 1 else 0) * f q.1.2) ∧ (NO.Pj d ρ).1 Φ = Φ := by
  obtain ⟨Φ0, hΦ0, -⟩ := SSTr.exists_tr P Bs hpl hk2 e he (fun _ => fnZ P f)
  refine ⟨(NO.Pj d ρ).1 Φ0, fun σ q => ?_, ?_⟩
  · show rawR P Bs.μsec e
        (((d.κ (fun ρ' => if ρ' = ρ then (1 : ℂ) else 0)).1 Φ0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
          Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q = _
    rw [kap_pt P Bs hpl hk2 e he d hk, ← SSTr.trR_apply P Bs hpl hk2 e he, hΦ0, fnZ_val P hf]
  · show ((NO.Pj d ρ) * (NO.Pj d ρ)).1 Φ0 = _
    rw [NO.Pj_idem]

end pt

theorem pt_of_tests {U : Set ℂ} (hU : IsOpen U) {H : ℂ → ℂ} (hH : ContinuousOn H U)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ ζ, φ ζ • H ζ = 0) :
    ∀ ζ0 ∈ U, H ζ0 = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (hH.locallyIntegrableOn hU.measurableSet) h
  intro ζ0 hζ0
  by_contra hne
  have hc : ContinuousAt H ζ0 := hH.continuousAt (hU.mem_nhds hζ0)
  have hev : ∀ᶠ x in nhds ζ0, H x ≠ 0 ∧ x ∈ U := (hc.eventually_ne hne).and (hU.mem_nhds hζ0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hpos := Metric.measure_ball_pos (volume : Measure ℂ) ζ0 hδ
  rw [ae_iff] at hae
  apply hpos.ne'
  apply measure_mono_null _ hae
  intro x hx
  have := hball x hx
  simp only [Set.mem_setOf_eq, not_forall, exists_prop]
  exact ⟨this.2, this.1⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdjH
