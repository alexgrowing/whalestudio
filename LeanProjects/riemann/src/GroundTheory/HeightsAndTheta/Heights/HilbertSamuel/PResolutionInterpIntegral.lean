import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionInterpIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionPotentials
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem locDens_resPot_interp (d : HSMDatum D Ω κ) {m₁ : ConeMetric ℂ (Ix κ)} (hm₁ : IsSmoothMetric m₁)
    (t : ℝ) (j : Fin d.R.A.n) {y : Fin D → ℂ} (hy : y ∈ (d.R.A.chart j).target) :
    locDens d.R.A (fun _ => resPot d (interp d.m m₁ t)) j y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y := by
  let x0 := (d.R.A.chart j).symm y
  let γ : (Fin D → ℂ) → Ix κ → ℂ := fun y' => d.R.lift x0 ((d.R.A.chart j).symm y')
  have hV : IsOpen ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0) :=
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U x0)
  have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ≠ 0 := by
    filter_upwards [hV.mem_nhds ⟨hy, d.R.mem_U x0⟩] with y' hy'
    exact ⟨differentiableAt_pi.2 fun p => (d.R.holo x0 p j y' hy').differentiableAt,
      gaamix_ne_zero_of_mcPts (d.R.mem x0 _ hy'.2)⟩
  have hL : locDens d.R.A (fun _ => resPot d (interp d.m m₁ t)) j y =
      maDensity (fun k y' => purePot (interp d.m m₁ t) D k (γ y')) y := rfl
  have hR : ∀ i, locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y =
      maDensity (fun k y' => mixPot d.m m₁ D i k (γ y')) y := by
    intro i
    have e : (fun (k : Fin D) (y' : Fin D → ℂ) =>
        (if k.val < i then resPot d m₁ else resPot d d.m).φ x0 ((d.R.A.chart j).symm y')) =
        fun k y' => mixPot d.m m₁ D i k (γ y') := by
      funext k y'
      by_cases hk : k.val < i
      · simp only [hk, if_true, mixPot]
        rfl
      · simp only [hk, if_false, mixPot]
        rfl
    show ReciprocityTheory.AnForm.maDens _ y = _
    rw [e]
    rfl
  rw [hL, gbamix_maDensity_interp d.smooth hm₁ t hγ]
  exact Finset.sum_congr rfl fun i _ => by rw [hR i]

theorem mInt_resPot_interp (d : HSMDatum D Ω κ) {m₁ : ConeMetric ℂ (Ix κ)} (hm₁ : IsSmoothMetric m₁)
    (t : ℝ) :
    mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) (fun y => logRatio d.m m₁ (resPt d y)) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        mInt d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m)
          (fun y => logRatio d.m m₁ (resPt d y)) := by
  have hg : Continuous (fun y => logRatio d.m m₁ (resPt d y)) :=
    continuous_logRatio_resPt d d.smooth hm₁
  have hΦ : ∀ (i : ℕ) (k : Fin D),
      IsPotential d.R.A (if k.val < i then resPot d m₁ else resPot d d.m) := by
    intro i k
    split_ifs
    · exact isPotential_resPot d hm₁
    · exact isPotential_resPot d d.smooth
  unfold mInt
  by_cases hP : Nonempty (ChartPartition d.R.A)
  · simp only [dif_pos hP]
    unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : ∀ i ∈ Finset.range (D + 1), Integrable (fun y =>
        (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
          (hP.some.χ j ((d.R.A.chart j).symm y) * logRatio d.m m₁ (resPt d ((d.R.A.chart j).symm y)) *
            locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y))
        (volume.restrict (d.R.A.chart j).target) := fun i _ =>
      (integrableOn_weight d.R.A hP.some _ _ (mIntegrableCont d.R.A _ (hΦ i) _ hg) j).const_mul _
    calc _ = ∫ y in (d.R.A.chart j).target, ∑ i ∈ Finset.range (D + 1),
          (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
            (hP.some.χ j ((d.R.A.chart j).symm y) *
              logRatio d.m m₁ (resPt d ((d.R.A.chart j).symm y)) *
              locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y) := by
          refine setIntegral_congr_fun (d.R.A.chart j).open_target.measurableSet fun y hy => ?_
          rw [locDens_resPot_interp d hm₁ t j hy, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [integral_finsetSum _ hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp only [dif_neg hP, mul_zero, Finset.sum_const_zero]

namespace ResolutionInterpIntegral

theorem proof : ResolutionInterpIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  unfold resMetricInt
  simp only [mInt_resPot_interp d hm₁]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_mul_const,
    ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein D i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end ResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
