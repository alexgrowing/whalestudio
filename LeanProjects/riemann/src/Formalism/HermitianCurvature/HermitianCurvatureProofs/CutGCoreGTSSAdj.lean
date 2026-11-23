import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSAdjH
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRadAdj

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdj

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.NFx4 Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdjH

noncomputable section

section blocks

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
  {d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))}

theorem shift_block_lower_component (hRel : d.Rel) (hQQ : ∀ Y : ℂ, X.QQ Y = d.QQ Y) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    {ρ ρ' : M.Ty P} (hU : M.Up P l ρ ρ') (Y : ℂ) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (NO.Pj d ρ').1 (X.t Y 1 0 ((NO.Pj d ρ).1 Z)) = M.xEx P {l} ρ Y • (NO.Pj d ρ').1 ((d.SS l).1 ((NO.Pj d ρ).1 Z)) := by
  have h : (NO.Pj d ρ' * d.QQ Y 1 0 * NO.Pj d ρ).1 Z = (M.xEx P {l} ρ Y • (NO.Pj d ρ' * d.SS l * NO.Pj d ρ)).1 Z :=
    congrArg (fun p : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => p.1 Z) (NO.B1 hRel hl hU Y)
  rw [← hQQ Y] at h
  exact h

theorem shift_block_upper_component (hRel : d.Rel) (hQQ : ∀ Y : ℂ, X.QQ Y = d.QQ Y) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    {ρ ρ' : M.Ty P} (hU : M.Up P l ρ ρ') (Y : ℂ) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (NO.Pj d ρ).1 (X.t Y 0 1 ((NO.Pj d ρ').1 Z)) =
      M.xEx P {l} ρ Y • (NO.Pj d ρ).1 ((star (d.SS l)).1 ((NO.Pj d ρ').1 Z)) := by
  have h : (NO.Pj d ρ * d.QQ Y 0 1 * NO.Pj d ρ').1 Z =
      (M.xEx P {l} ρ Y • (NO.Pj d ρ * star (d.SS l) * NO.Pj d ρ')).1 Z :=
    congrArg (fun p : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => p.1 Z) (NO.B4 hRel hl hU Y)
  rw [← hQQ Y] at h
  exact h

theorem blk_zero (hRel : d.Rel) {l : ℕ} {ρ ρ' : M.Ty P} (hU : ¬ M.Up P l ρ ρ')
    (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (NO.Pj d ρ').1 ((d.SS l).1 ((NO.Pj d ρ).1 Z)) = 0 := by
  have h : (NO.Pj d ρ' * d.SS l * NO.Pj d ρ).1 Z = (0 : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')).1 Z :=
    congrArg (fun p : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => p.1 Z) (NO.block_zero hRel hU)
  exact h

theorem blk_zero_star (hRel : d.Rel) {l : ℕ} {ρ ρ' : M.Ty P} (hU : ¬ M.Up P l ρ ρ')
    (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    (NO.Pj d ρ).1 ((star (d.SS l)).1 ((NO.Pj d ρ').1 Z)) = 0 := by
  have h : (NO.Pj d ρ * star (d.SS l) * NO.Pj d ρ').1 Z = (0 : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')).1 Z :=
    congrArg (fun p : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => p.1 Z) (NO.star_block_zero hRel hU)
  exact h

end blocks

section pj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pj_pt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk2 : 2 ≤ P.k)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hk : KapF P Bs d e) (ρ : M.Ty P)
    (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e (((NO.Pj d ρ).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
      (if σ = ρ then 1 else 0) * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q :=
  kap_pt P Bs hpl hk2 e he d hk _ Z σ q

end pj

theorem xEx_ne (P : M.Par) (l : ℕ) (ρ : M.Ty P) :
    M.xEx P {l} ρ (((1 + ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P ρ i| : ℝ)) : ℂ) ≠ 0 := by
  unfold M.xEx
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi' : i ∈ Finset.Icc 1 (P.k - 1) := (Finset.mem_sdiff.1 hi).1
  have h1 : |M.rho P ρ i| ≤ ∑ j ∈ Finset.Icc 1 (P.k - 1), |M.rho P ρ j| :=
    Finset.single_le_sum (f := fun j => |M.rho P ρ j|) (fun j _ => abs_nonneg _) hi'
  have h2 : 0 < 1 + ∑ j ∈ Finset.Icc 1 (P.k - 1), |M.rho P ρ j| + M.rho P ρ i := by
    have := neg_abs_le (M.rho P ρ i)
    linarith
  have h3 : ((1 + ∑ j ∈ Finset.Icc 1 (P.k - 1), |M.rho P ρ j| + M.rho P ρ i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h2.ne'
  push_cast at h3 ⊢
  exact h3

theorem xEx_star (P : M.Par) (l : ℕ) (ρ : M.Ty P) (Y : ℝ) : star (M.xEx P {l} ρ (Y : ℂ)) = M.xEx P {l} ρ (Y : ℂ) := by
  unfold M.xEx
  show (starRingEnd ℂ) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_add, Complex.conj_ofReal, Complex.conj_ofReal]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdj

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdj Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdjH Formalism.FourierDecayAlt.P.NFx4 in
theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTSSAdjPt_of_radAdj : GTRadAdj → GTSSAdjPt := by
  intro hRA Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk s t hst hL l hl ρ ρ' ζ0 hζ0
  have hpl := hH.1
  have hk2 := hH.2.1
  have hRel := hH.2.2.2.2.2.1
  have hQQ := hH.2.2.2.2.2.2
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  let qOf : ∀ ζ : ℂ, ζ ∈ Ann P → MA.Qp P.r P.TT := fun ζ hζ => ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  by_cases hU : M.Up P l ρ ρ'
  ·
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (ann_open P) ζ0 hζ0
    set r : ℝ := ε / 3 with hrdef
    have hr : 0 < r := by rw [hrdef]; linarith
    have hK : Metric.closedBall ζ0 (2 * r) ⊆ Ann P :=
      (Metric.closedBall_subset_ball (by rw [hrdef]; linarith)).trans hball
    have hBr : Metric.ball ζ0 r ⊆ Ann P := (Metric.ball_subset_ball (by rw [hrdef]; linarith)).trans hball
    set Yr : ℝ := 1 + ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P ρ i| with hYr
    set x : ℂ := M.xEx P {l} ρ (Yr : ℂ) with hxdef
    have hx : x ≠ 0 := xEx_ne P l ρ
    have hxs : star x = x := xEx_star P l ρ Yr
    have hYs : star (Yr : ℂ) = (Yr : ℂ) := Complex.conj_ofReal Yr
    let χ : ContDiffBump ζ0 := ⟨r, 2 * r, hr, by linarith⟩
    set g : ℂ → ℂ := fun ζ => ((χ ζ : ℝ) : ℂ) with hgdef
    have hgc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := Complex.ofRealCLM.contDiff.comp χ.contDiff
    have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (Ann P) := hgc.contDiffOn
    have hg1 : ∀ ζ ∈ Metric.closedBall ζ0 r, g ζ = 1 := by
      intro ζ hζ
      simp only [hgdef, χ.one_of_mem_closedBall hζ, Complex.ofReal_one]
    have hg0 : ∀ ζ, ζ ∉ Metric.closedBall ζ0 (2 * r) → g ζ = 0 := by
      intro ζ hζ
      have h0 : χ ζ = 0 := by
        by_contra h
        have hs : ζ ∈ Function.support χ := h
        rw [χ.support_eq] at hs
        exact hζ (Metric.ball_subset_closedBall hs)
      simp only [hgdef, h0, Complex.ofReal_zero]
    obtain ⟨Ψ, hΨr, hΨp⟩ := exists_proj P Bs hpl hk2 e he d hk g hg ρ'
    set H : ℂ → ℂ := fun ζ => x * (star (s l ρ' ρ ζ) - t l ρ ρ' ζ) with hHdef
    have hsc : ContinuousOn (s l ρ' ρ) (Ann P) := (hst l ρ' ρ).1.continuousOn
    have htc : ContinuousOn (t l ρ ρ') (Ann P) := (hst l ρ ρ').2.continuousOn
    have hHc : ContinuousOn H (Ann P) :=
      continuousOn_const.mul ((continuous_star.comp_continuousOn hsc).sub htc)
    suffices hH0 : H ζ0 = 0 by
      have h1 : star (s l ρ' ρ ζ0) - t l ρ ρ' ζ0 = 0 := (mul_eq_zero.1 hH0).resolve_left hx
      exact (sub_eq_zero.1 h1).symm
    refine pt_of_tests Metric.isOpen_ball (hHc.mono hBr) (fun φ hφ hφc hφs => ?_) ζ0 (Metric.mem_ball_self hr)
    set f : ℂ → ℂ := fun ζ => ((φ ζ : ℝ) : ℂ) with hfdef
    have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ann P) :=
      (Complex.ofRealCLM.contDiff.comp hφ).contDiffOn
    have hφ0 : ∀ ζ, ζ ∉ Metric.ball ζ0 r → φ ζ = 0 := fun ζ hζ =>
      image_eq_zero_of_notMem_tsupport (fun h => hζ (hφs h))
    have hfg : ∀ ζ, ((φ ζ : ℝ) : ℂ) * g ζ = ((φ ζ : ℝ) : ℂ) := by
      intro ζ
      by_cases hζ : ζ ∈ Metric.closedBall ζ0 r
      · rw [hg1 ζ hζ, mul_one]
      · rw [hφ0 ζ (fun h => hζ (Metric.ball_subset_closedBall h))]
        simp
    obtain ⟨Φ, hΦr, hΦp⟩ := exists_proj P Bs hpl hk2 e he d hk f hf ρ

    have hT1 : ∀ q : MA.Qp P.r P.TT, rawR P Bs.μsec e ((X.t (Yr : ℂ) 1 0 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q = x * (s l ρ' ρ q.1.2 * f q.1.2) := by
      intro q
      have hb := shift_block_lower_component hRel hQQ hl hU (Yr : ℂ) Φ
      rw [hΦp] at hb
      have h1 := pj_pt P Bs hpl hk2 e he d hk ρ' (X.t (Yr : ℂ) 1 0 Φ) ρ' q
      rw [if_pos rfl, one_mul] at h1
      rw [← h1, hb, Submodule.coe_smul, rawR_smul, pj_pt P Bs hpl hk2 e he d hk, if_pos rfl, one_mul,
        (ss_pt P Bs hpl hk2 e he d s t hst hL hl Φ ρ' q).1]
      congr 1
      rw [Finset.sum_eq_single ρ (fun σ _ hσ => by rw [hΦr, if_neg hσ, zero_mul, mul_zero]) (by simp), hΦr,
        if_pos rfl, one_mul]
    have hT2 : ∀ q : MA.Qp P.r P.TT, rawR P Bs.μsec e ((X.t (Yr : ℂ) 0 1 Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = x * (t l ρ ρ' q.1.2 * g q.1.2) := by
      intro q
      have hb := shift_block_upper_component hRel hQQ hl hU (Yr : ℂ) Ψ
      rw [hΨp] at hb
      have h1 := pj_pt P Bs hpl hk2 e he d hk ρ (X.t (Yr : ℂ) 0 1 Ψ) ρ q
      rw [if_pos rfl, one_mul] at h1
      rw [← h1, hb, Submodule.coe_smul, rawR_smul, pj_pt P Bs hpl hk2 e he d hk, if_pos rfl, one_mul,
        (ss_pt P Bs hpl hk2 e he d s t hst hL hl Ψ ρ q).2]
      congr 1
      rw [Finset.sum_eq_single ρ' (fun σ _ hσ => by rw [hΨr, if_neg hσ, zero_mul, mul_zero]) (by simp), hΨr,
        if_pos rfl, one_mul]

    have hvan : ∃ K : Set ℂ, IsCompact K ∧ K ⊆ Ann P ∧ ∀ ζ ∈ Ann P, ζ ∉ K →
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) = 0 ∧
          (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) = 0 := by
      refine ⟨Metric.closedBall ζ0 (2 * r), isCompact_closedBall _ _, hK, fun ζ hζ hnK => ⟨?_, ?_⟩⟩
      · have hfz : f ζ = 0 := by
          rw [hfdef]
          simp only
          rw [hφ0 ζ (fun h => hnK ((Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall h))]
          simp
        refine (sec_expand P Bs hpl hk2 e he Φ (qOf ζ hζ)).trans (Finset.sum_eq_zero fun σ _ => ?_)
        rw [hΦr]
        show (_ * ((if σ = ρ then 1 else 0) * f ζ)) • _ = _
        rw [hfz, mul_zero, mul_zero, zero_smul]
      · refine (sec_expand P Bs hpl hk2 e he Ψ (qOf ζ hζ)).trans (Finset.sum_eq_zero fun σ _ => ?_)
        rw [hΨr]
        show (_ * ((if σ = ρ' then 1 else 0) * g ζ)) • _ = _
        rw [hg0 ζ hnK, mul_zero, mul_zero, zero_smul]
    have hRA' := hRA Wp Wq P Bs X d hH (Yr : ℂ) 1 0 c0 hc0 Φ Ψ hvan
    rw [hYs] at hRA'

    have hmA : MeasurableSet (Ann P) := (ann_open P).measurableSet
    have hI1 : ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((X.t (Yr : ℂ) 1 0 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ))) =
        ∫ ζ in Ann P, star (x * (s l ρ' ρ ζ * f ζ)) * g ζ := by
      refine setIntegral_congr_fun hmA fun ζ hζ => ?_
      refine (hs_pair P Bs hpl hk2 e he (X.t (Yr : ℂ) 1 0 Φ) Ψ (qOf ζ hζ)).trans ?_
      rw [Finset.sum_eq_single ρ' (fun σ _ hσ => by rw [hΨr, if_neg hσ, zero_mul, mul_zero]) (by simp), hΨr,
        if_pos rfl, one_mul, hT1]
    have hI2 : ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((X.t (Yr : ℂ) 0 1 Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ))) =
        ∫ ζ in Ann P, star (f ζ) * (x * (t l ρ ρ' ζ * g ζ)) := by
      refine setIntegral_congr_fun hmA fun ζ hζ => ?_
      refine (hs_pair P Bs hpl hk2 e he Φ (X.t (Yr : ℂ) 0 1 Ψ) (qOf ζ hζ)).trans ?_
      rw [Finset.sum_eq_single ρ (fun σ _ hσ => by rw [hΦr, if_neg hσ, zero_mul, star_zero, zero_mul]) (by simp),
        hΦr, if_pos rfl, one_mul, hT2]
    rw [hI1, hI2] at hRA'

    have hfc : Continuous f := (Complex.ofRealCLM.contDiff.comp hφ).continuous
    have hgcc : Continuous g := hgc.continuous
    have hIA : IntegrableOn (fun ζ => star (x * (s l ρ' ρ ζ * f ζ)) * g ζ) (Ann P) volume := by
      have hc : ContinuousOn (fun ζ => star (x * (s l ρ' ρ ζ * f ζ)) * g ζ) (Metric.closedBall ζ0 (2 * r)) :=
        ((continuous_star.comp_continuousOn
          (continuousOn_const.mul ((hsc.mono hK).mul hfc.continuousOn))).mul hgcc.continuousOn)
      exact (hc.integrableOn_compact (isCompact_closedBall _ _)).of_forall_sdiff_eq_zero hmA
        fun ζ hζ => by simp [hg0 ζ hζ.2]
    have hIB : IntegrableOn (fun ζ => star (f ζ) * (x * (t l ρ ρ' ζ * g ζ))) (Ann P) volume := by
      have hc : ContinuousOn (fun ζ => star (f ζ) * (x * (t l ρ ρ' ζ * g ζ))) (Metric.closedBall ζ0 (2 * r)) :=
        (continuous_star.comp hfc).continuousOn.mul
          (continuousOn_const.mul ((htc.mono hK).mul hgcc.continuousOn))
      exact (hc.integrableOn_compact (isCompact_closedBall _ _)).of_forall_sdiff_eq_zero hmA
        fun ζ hζ => by simp [hg0 ζ hζ.2]
    have hdiff : ∫ ζ in Ann P, (star (x * (s l ρ' ρ ζ * f ζ)) * g ζ - star (f ζ) * (x * (t l ρ ρ' ζ * g ζ))) = 0 := by
      rw [integral_sub hIA hIB, hRA', sub_self]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ann P) (fun ζ hζ => by
      rw [hφ0 ζ (fun h => hζ (hBr h)), zero_smul])]
    rw [← hdiff]
    refine setIntegral_congr_fun hmA fun ζ _ => ?_
    have hfs : star (f ζ) = f ζ := Complex.conj_ofReal _
    show (φ ζ) • (x * (star (s l ρ' ρ ζ) - t l ρ ρ' ζ)) = _
    rw [Complex.real_smul, star_mul', star_mul', hxs, hfs]
    have := hfg ζ
    rw [hfdef]
    simp only
    linear_combination (x * t l ρ ρ' ζ - x * star (s l ρ' ρ ζ)) * this
  ·
    obtain ⟨U0, hU0r, hU0p⟩ := exists_proj P Bs hpl hk2 e he d hk (fun _ => 1) contDiffOn_const ρ
    obtain ⟨V0, hV0r, hV0p⟩ := exists_proj P Bs hpl hk2 e he d hk (fun _ => 1) contDiffOn_const ρ'
    have hs0 : s l ρ' ρ ζ0 = 0 := by
      have h0 := blk_zero hRel hU U0
      have h1 := pj_pt P Bs hpl hk2 e he d hk ρ' ((d.SS l).1 ((NO.Pj d ρ).1 U0)) ρ' (qOf ζ0 hζ0)
      rw [h0, if_pos rfl, one_mul, Submodule.coe_zero, rawR_zero, hU0p,
        (ss_pt P Bs hpl hk2 e he d s t hst hL hl U0 ρ' (qOf ζ0 hζ0)).1,
        Finset.sum_eq_single ρ (fun σ _ hσ => by rw [hU0r, if_neg hσ, zero_mul, mul_zero]) (by simp), hU0r,
        if_pos rfl, one_mul, mul_one] at h1
      exact h1.symm
    have ht0 : t l ρ ρ' ζ0 = 0 := by
      have h0 := blk_zero_star hRel hU V0
      have h1 := pj_pt P Bs hpl hk2 e he d hk ρ ((star (d.SS l)).1 ((NO.Pj d ρ').1 V0)) ρ (qOf ζ0 hζ0)
      rw [h0, if_pos rfl, one_mul, Submodule.coe_zero, rawR_zero, hV0p,
        (ss_pt P Bs hpl hk2 e he d s t hst hL hl V0 ρ (qOf ζ0 hζ0)).2,
        Finset.sum_eq_single ρ' (fun σ _ hσ => by rw [hV0r, if_neg hσ, zero_mul, mul_zero]) (by simp), hV0r,
        if_pos rfl, one_mul, mul_one] at h1
      exact h1.symm
    rw [hs0, ht0, star_zero]

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.second_shift_adjoint_pointwise : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTSSAdjPt :=
  Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTSSAdjPt_of_radAdj Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.radial_adjoint_identity_holds
