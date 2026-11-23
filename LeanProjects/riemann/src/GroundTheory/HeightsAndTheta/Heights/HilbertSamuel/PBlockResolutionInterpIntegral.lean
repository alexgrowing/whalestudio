import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionInterpIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

namespace BlockResolutionInterpIntegral

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem locDens_interp (d : HSMBlockDatum D K ι Ω) {A' : HermLine ι} (hA' : IsSmoothHerm A')
    (t : ℝ) (j : Fin d.R.A.n) {y : Fin D → ℂ} (hy : y ∈ (d.R.A.chart j).target) :
    locDens d.R.A (fun _ => blockInterpPot d d.A A' t) j y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
          else AnResBridge.potOf d.R d.A) j y := by
  set x0 := (d.R.A.chart j).symm y with hx0
  set a : (Fin D → ℂ) → ℝ := fun y' => Real.log (d.A.h (d.R.lift x0 ((d.R.A.chart j).symm y'))) with ha
  set b : (Fin D → ℂ) → ℝ := fun y' => Real.log (A'.h (d.R.lift x0 ((d.R.A.chart j).symm y'))) with hb
  have hV : IsOpen ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0) :=
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U x0)
  have hyV : y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0 := ⟨hy, d.R.mem_U x0⟩
  have hsm : ∀ {L : HermLine ι}, IsSmoothHerm L → ∀ᶠ y' in 𝓝 y,
      ContDiffAt ℝ 2 (fun y'' => Real.log (L.h (d.R.lift x0 ((d.R.A.chart j).symm y'')))) y' := by
    intro L hL
    filter_upwards [hV.mem_nhds hyV] with y' hy'
    exact_mod_cast contDiffAt_infty.mp
      ((AnResBridge.contDiffOn_potOf d.R hL x0 j).contDiffAt (hV.mem_nhds hy')) 2
  have hH := gaamix_cxHessian_comb (ψ := fun y' => (1 - t) * a y' + t * b y') (1 - t) t
    (hsm d.semipos.1) (hsm hA') (Filter.EventuallyEq.refl _ _)
  set H₀ := cxHessian a y
  set H₁ := cxHessian b y
  have hL : locDens d.R.A (fun _ => blockInterpPot d d.A A' t) j y =
      ReciprocityTheory.AnForm.maDens (fun _ y' => (1 - t) * a y' + t * b y') y := rfl
  have hR : ∀ i, locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
      else AnResBridge.potOf d.R d.A) j y =
      ReciprocityTheory.AnForm.maDens (fun k => if k.val < i then b else a) y := by
    intro i
    show ReciprocityTheory.AnForm.maDens _ y = _
    congr 1
    funext k y'
    by_cases hk : k.val < i
    · simp only [hk, if_true]; rfl
    · simp only [hk, if_false]; rfl
  have hpure : (fun _ : Fin D => ReciprocityTheory.AnForm.hessC (fun y' => (1 - t) * a y' + t * b y') y) =
      fun _ => (t : ℂ) • H₁ + (1 - (t : ℂ)) • H₀ := by
    funext k
    show cxHessian _ y = _
    rw [hH, add_comm]
    push_cast
    rfl
  have hmix : ∀ i, (fun k : Fin D => ReciprocityTheory.AnForm.hessC (if k.val < i then b else a) y) =
      fun k : Fin D => if k.val < i then H₁ else H₀ := by
    intro i
    funext k
    by_cases hk : k.val < i
    · simp only [hk, if_true]; rfl
    · simp only [hk, if_false]; rfl
  rw [hL]
  simp only [hR]
  unfold ReciprocityTheory.AnForm.maDens
  rw [hpure, ReciprocityTheory.AnForm.A.mdisc_const, ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmix i]
  have e : (D.choose i : ℂ) * (t : ℂ) ^ i * (1 - (t : ℂ)) ^ (D - i) =
      ((D.choose i * t ^ i * (1 - t) ^ (D - i) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  ring

theorem continuous_logRatio (d : HSMBlockDatum D K ι Ω) {A' : HermLine ι} (hdeg : A'.a = unitDeg d.k₀)
    (hA' : IsSmoothHerm A') :
    Continuous fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x)) := by
  have hA : IsSmoothHerm d.A := d.semipos.1
  have hE : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
      ext z; simp
    rw [e]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hΦ : ContinuousOn (fun z : (Σ k, ι k) → ℂ => Real.log (A'.h z / d.A.h z))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hA'.continuousOn.div hA.continuousOn fun z hz => (d.A.pos z hz).ne').log fun z hz =>
      (div_pos (A'.pos z hz) (d.A.pos z hz)).ne'
  have hdeg' : A'.a = d.A.a := hdeg.trans d.deg.symm
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hU := (d.R.isOpen_U x₀).mem_nhds (d.R.mem_U x₀)
  have hl : ContinuousAt (d.R.lift x₀) x₀ :=
    (continuousOn_pi.2 fun p => AnResBridge.continuousOn_lift d.R x₀ p).continuousAt hU
  have h0 : d.R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (d.R.mem x₀ x₀ (d.R.mem_U x₀)).1
  have h2 : ContinuousAt (fun x => Real.log (A'.h (d.R.lift x₀ x) / d.A.h (d.R.lift x₀ x))) x₀ :=
    (hΦ.continuousAt (hE.mem_nhds h0)).comp hl
  refine h2.congr ?_
  filter_upwards [hU] with x hx
  obtain ⟨c, hc0, he⟩ := d.R.compat x x₀ x ⟨d.R.mem_U x, hx⟩
  show _ = Real.log (A'.h (d.R.lift x x) / d.A.h (d.R.lift x x))
  have hp : (∏ k, ‖c k‖ ^ d.A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc0 k))
  rw [he, A'.smul c _ hc0, d.A.smul c _ hc0, hdeg', mul_div_mul_left _ _ hp]

theorem mInt_interp (d : HSMBlockDatum D K ι Ω) {A' : HermLine ι} (hdeg : A'.a = unitDeg d.k₀)
    (hA' : IsSmoothHerm A') (t : ℝ) :
    mInt d.R.A (fun _ => blockInterpPot d d.A A' t)
        (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        mInt d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
            else AnResBridge.potOf d.R d.A)
          (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))) := by
  have hg := continuous_logRatio d hdeg hA'
  have hΦ : ∀ (i : ℕ) (k : Fin D), IsPotential d.R.A
      (if k.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A) := by
    intro i k
    split_ifs
    · exact AnResBridge.isPotential_potOf d.R hA'
    · exact AnResBridge.isPotential_potOf d.R d.semipos.1
  unfold mInt
  by_cases hP : Nonempty (ChartPartition d.R.A)
  · simp only [dif_pos hP]
    unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : ∀ i ∈ Finset.range (D + 1), Integrable (fun y =>
        (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
          (hP.some.χ j ((d.R.A.chart j).symm y) *
            Real.log (A'.h (blockPt d ((d.R.A.chart j).symm y)) / d.A.h (blockPt d ((d.R.A.chart j).symm y))) *
            locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
              else AnResBridge.potOf d.R d.A) j y))
        (volume.restrict (d.R.A.chart j).target) := fun i _ =>
      (integrableOn_weight d.R.A hP.some _ _ (mIntegrableCont d.R.A _ (hΦ i) _ hg) j).const_mul _
    calc _ = ∫ y in (d.R.A.chart j).target, ∑ i ∈ Finset.range (D + 1),
          (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
            (hP.some.χ j ((d.R.A.chart j).symm y) *
              Real.log (A'.h (blockPt d ((d.R.A.chart j).symm y)) /
                d.A.h (blockPt d ((d.R.A.chart j).symm y))) *
              locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
                else AnResBridge.potOf d.R d.A) j y) := by
          refine setIntegral_congr_fun (d.R.A.chart j).open_target.measurableSet fun y hy => ?_
          rw [locDens_interp d hA' t j hy, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [integral_finsetSum _ hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp only [dif_neg hP, mul_zero, Finset.sum_const_zero]

theorem proof : BlockResolutionInterpIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' hdeg hA'
  unfold blockMetricInt
  simp only [mInt_interp d hdeg hA']
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_mul_const,
    ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein D i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end BlockResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
