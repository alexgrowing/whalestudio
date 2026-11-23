import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.AnalyticForms.LeviForms.MixedIntegralInclusionExclusion
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensAddOfFunContinuousOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyUniformBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralRegularizedConvergenceStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.Conv

open GroundTheory.Heights₂.Heights.AnalyticLimit (TailLogBound tail)

theorem tailLogBound_congr_φ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Yo : Set X) (r : X → ℝ) {Φ Ψ : Fin e → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ) (CE : ℝ)
    (H : TailLogBound A Yo r Φ CE) : TailLogBound A Yo r Ψ CE := by
  have hD : locDens A Φ = locDens A Ψ := by
    funext j y
    simp only [locDens, h]
  intro R₀ hR
  obtain ⟨h1, h2⟩ := H R₀ hR
  refine ⟨?_, ?_⟩
  · unfold MIntegrable at h1 ⊢
    rw [← hD]
    exact h1
  · unfold mInt integralWith at h2 ⊢
    rw [← hD]
    exact h2

theorem isPsh_reassoc {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (a Θ : LocPot X) (v : X → ℝ) (h : IsPsh A (a + LocPot.ofFun v + Θ)) :
    IsPsh A (a + Θ + LocPot.ofFun v) := by
  intro x j y hy w
  have h1 := h x j y ⟨hy.1, ⟨⟨hy.2.1.1, trivial⟩, hy.2.1.2⟩⟩ w
  have h2 : (a + Θ + LocPot.ofFun v).φ x = (a + LocPot.ofFun v + Θ).φ x := by
    funext z
    change a.φ x z + Θ.φ x z + v z = a.φ x z + v z + Θ.φ x z
    ring
  rw [h2]
  exact h1

theorem position_tail (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X)
    (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (P : Fin e → LocPot X) (C : ℝ)
    (hP : ∀ i, IsPotential A (P i)) (T : Finset (Fin e)) :
    ∃ CE : ℝ, ∀ u : Fin e → X → ℝ, (∀ i, A.Smooth (u i)) →
      (∀ i, IsPsh A (P i + LocPot.ofFun (u i) + Θ)) →
      (∀ i, ∀ x ∈ R.Yo, |u i x| ≤ C + C * Real.log (R.r x) ∧ u i x ≤ C) →
      (∀ i, IsPsh A ((if i ∈ T then P i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then u i else 0) + Θ)) ∧
      TailLogBound A R.Yo R.r (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then u i else 0) + Θ) CE := by
  have hz : A.Smooth (0 : X → ℝ) := fun j => contDiffOn_const
  have hth : ∀ i, IsPotential A ((if i ∈ T then P i else LocPot.ofFun 0) + Θ) := by
    intro i
    refine isPotentialAdd A _ _ ?_ hΘ
    split_ifs
    · exact hP i
    · exact isPotential_ofFun A _ hz
  obtain ⟨CE, hCE⟩ := GlobalTheory.T.mixed_energy_uniform_bound e X A R Θ hΘ hΘp
    (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + Θ) |C| hth
  refine ⟨CE, fun u hu hpsh hb => ?_⟩
  have h1 : ∀ i, IsPsh A ((if i ∈ T then P i else LocPot.ofFun 0) +
      LocPot.ofFun (if i ∈ T then u i else 0) + Θ) := by
    intro i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact hpsh i
    · simp only [hi, if_false]
      intro x j y hy w
      have h3 := ReciprocityTheory.AnForm.P.TailBoundAlt.isPsh_of_isPosPot A Θ hΘp x j y ⟨hy.1, hy.2.2⟩ w
      have h2 : (LocPot.ofFun (0 : X → ℝ) + LocPot.ofFun 0 + Θ).φ x = Θ.φ x := by
        funext z
        change (0 : ℝ) + 0 + Θ.φ x z = Θ.φ x z
        ring
      rw [h2]
      exact h3
  refine ⟨h1, ?_⟩
  have hlog : ∀ x ∈ R.Yo, 0 ≤ Real.log (R.r x) := fun x hx => Real.log_nonneg (R.one_le_r x hx)
  have h4 := hCE (fun i => if i ∈ T then u i else 0) ?_ (fun i => isPsh_reassoc A _ _ _ (h1 i)) ?_ ?_
  · refine tailLogBound_congr_φ A _ _ (fun i => ?_) CE h4
    funext x z
    change _ + Θ.φ x z + _ = _ + _ + Θ.φ x z
    ring
  · intro i
    split_ifs
    · exact hu i
    · exact hz
  · intro i x hx
    have hC : C + C * Real.log (R.r x) ≤ |C| + |C| * Real.log (R.r x) :=
      add_le_add (le_abs_self C) (mul_le_mul_of_nonneg_right (le_abs_self C) (hlog x hx))
    split_ifs
    · exact (hb i x hx).1.trans hC
    · simp only [Pi.zero_apply, abs_zero]
      have hz0 : 0 ≤ |C| + |C| * Real.log (R.r x) :=
        add_nonneg (abs_nonneg C) (mul_nonneg (abs_nonneg C) (hlog x hx))
      exact hz0
  · intro i x hx
    split_ifs
    · exact (hb i x hx).2.trans (le_abs_self C)
    · simp [abs_nonneg]

theorem expand_on {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Yo : Set X)
    (hYo : IsOpen Yo) (hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yoᶜ) = 0)
    (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X) (hP : ∀ i, IsPotential A (P i))
    (hΘ : IsPotential A Θ) (hf : ∀ i, A.SmoothOn Yo (f i)) (j : Fin A.n)
    (K : Set (Fin e → ℂ)) (hKm : MeasurableSet K) (hKt : K ⊆ (A.chart j).target)
    (w : (Fin e → ℂ) → ℝ)
    (hI : ∀ T : Finset (Fin e), IntegrableOn (fun y => w y * locDens A (fun i =>
      (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y) K) :
    IntegrableOn (fun y => w y * locDens A (fun i => P i + LocPot.ofFun (f i)) j y) K ∧
      ∫ y in K, w y * locDens A (fun i => P i + LocPot.ofFun (f i)) j y =
        ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * ∫ y in K, w y * locDens A (fun i =>
          (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
  have hae0 : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ (A.chart j).target →
      (A.chart j).symm y ∈ Yo := by
    rw [ae_iff]
    refine measure_mono_null ?_ (hnull j)
    intro y hy
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hy
    exact ⟨hy.1, hy.2⟩
  have hae : (fun y => w y * locDens A (fun i => P i + LocPot.ofFun (f i)) j y) =ᵐ[volume.restrict K]
      fun y => ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * (w y * locDens A (fun i =>
        (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y) := by
    refine (ae_restrict_iff' hKm).2 ?_
    filter_upwards [hae0] with y hy hyK
    rw [GlobalTheory.T.local_density_inclusion_exclusion A Yo P f Θ hYo hP hΘ hf j y ⟨hKt hyK, hy (hKt hyK)⟩, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  have hint := fun T (_ : T ∈ (Finset.univ : Finset (Finset (Fin e)))) => (hI T).const_mul ((-1 : ℝ) ^ (e - T.card))
  refine ⟨(integrable_finset_sum _ hint).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_finset_sum _ hint]
  simp_rw [integral_const_mul]

theorem mIntegrable_of_logBound {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A)
    (Φ : Fin e → LocPot X) (CE C : ℝ) (g : X → ℝ) (hΦ : ∀ i, IsPotential A (Φ i))
    (hdens : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ R.Yo → 0 ≤ locDens A Φ j y)
    (hT : TailLogBound A R.Yo R.r Φ CE)
    (hg : @Measurable X ℝ (borel X) _ (R.Yo.indicator g))
    (hgb : ∀ x ∈ R.Yo, |g x| ≤ C + C * Real.log (R.r x)) : MIntegrable A Φ g := by
  intro j K hK hKc
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  obtain ⟨-, hnull, -, -⟩ := GlobalTheory.T.regular_chart_data_properties e X A R
  have hKm := hKc.measurableSet
  have hD : IntegrableOn (locDens A Φ j) K := ((locDensCont A Φ hΦ j).mono hK).integrableOn_compact hKc
  have hTl := (hT (Real.exp 1) le_rfl).1 j K hK hKc
  have hae : ∀ᵐ y ∂(volume.restrict K), y ∈ K ∧ (A.chart j).symm y ∈ R.Yo := by
    refine (ae_restrict_iff' hKm).2 ?_
    have h0 : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ (A.chart j).target →
        (A.chart j).symm y ∈ R.Yo := by
      rw [ae_iff]
      refine measure_mono_null ?_ (hnull j)
      intro y hy
      simp only [Set.mem_setOf_eq, Classical.not_imp] at hy
      exact ⟨hy.1, hy.2⟩
    filter_upwards [h0] with y hy hyK
    exact ⟨hyK, hy (hK hyK)⟩
  have hsm : AEMeasurable (A.chart j).symm (volume.restrict K) :=
    ((A.chart j).continuousOn_symm.mono hK).aemeasurable hKm
  have hm1 : AEStronglyMeasurable (fun y => g ((A.chart j).symm y)) (volume.restrict K) := by
    refine (hg.comp_aemeasurable hsm).aestronglyMeasurable.congr ?_
    filter_upwards [hae] with y hy
    simp [Function.comp, Set.indicator_of_mem hy.2]
  have hb : Integrable (fun y => 2 * |C| * locDens A Φ j y + 2 * |C| *
      ((tail R.Yo R.r (Real.exp 1)).indicator (fun x => Real.log (R.r x)) ((A.chart j).symm y) *
        locDens A Φ j y)) (volume.restrict K) :=
    (hD.const_mul _).add (hTl.const_mul _)
  refine hb.mono' (hm1.mul hD.aestronglyMeasurable) ?_
  filter_upwards [hae] with y hy
  have hd := hdens j y (hK hy.1) hy.2
  have hL := Real.log_nonneg (R.one_le_r _ hy.2)
  have hC := hgb _ hy.2
  have hC' : C + C * Real.log (R.r ((A.chart j).symm y)) ≤
      |C| + |C| * Real.log (R.r ((A.chart j).symm y)) :=
    add_le_add (le_abs_self C) (mul_le_mul_of_nonneg_right (le_abs_self C) hL)
  have hc0 := abs_nonneg C
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd]
  have key : |g ((A.chart j).symm y)| ≤ 2 * |C| + 2 * |C| *
      (tail R.Yo R.r (Real.exp 1)).indicator (fun x => Real.log (R.r x)) ((A.chart j).symm y) := by
    by_cases hr : Real.exp 1 ≤ R.r ((A.chart j).symm y)
    · rw [Set.indicator_of_mem (show _ ∈ tail R.Yo R.r (Real.exp 1) from ⟨hy.2, hr⟩)]
      nlinarith
    · rw [Set.indicator_of_notMem (fun h => hr h.2)]
      have hl1 : Real.log (R.r ((A.chart j).symm y)) ≤ 1 := by
        rw [Real.log_le_iff_le_exp (lt_of_lt_of_le one_pos (R.one_le_r _ hy.2))]
        exact (not_le.1 hr).le
      nlinarith
  calc |g ((A.chart j).symm y)| * locDens A Φ j y
      ≤ (2 * |C| + 2 * |C| *
        (tail R.Yo R.r (Real.exp 1)).indicator (fun x => Real.log (R.r x)) ((A.chart j).symm y)) *
          locDens A Φ j y := mul_le_mul_of_nonneg_right key hd
    _ = _ := by ring

end GlobalTheory.CompanionTheory.Ar.Giv.Conv

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GlobalTheory.CompanionTheory.Ar.Giv.Conv GroundTheory.Heights₂.Heights.AnalyticLimit in

theorem mixed_integral_tendsto_of_C2_off_divisor : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → ∀ (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (fT : Fin e → ℝ → X → ℝ) (G : X → ℝ) (GT : ℝ → X → ℝ) (C : ℝ), (∀ i, IsPotential A (P i)) → (∀ i, A.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, A.Smooth (fT i t) ∧ IsPsh A (P i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (A.chart j).symm) (f i ∘ (A.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (A.chart j).symm)) (fderiv ℝ (f i ∘ (A.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (A.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (A.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable X ℝ (borel X) _ (R.Yo.indicator (GT t)) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → MIntegrable A (fun i => P i + LocPot.ofFun (f i)) G ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => P i + LocPot.ofFun (fT i t)) (GT t)) ∧ Tendsto (fun t => mInt A (fun i => P i + LocPot.ofFun (fT i t)) (GT t)) (𝓝[>] 0) (𝓝 (mInt A (fun i => P i + LocPot.ofFun (f i)) G)) := by
  intro e X _ _ _ A R Θ hΘ hΘp P f fT G GT C hP hf hfT hC hGT hGc
  obtain ⟨hYo, hnull, -, -⟩ := GlobalTheory.T.regular_chart_data_properties e X A R
  have hz : A.Smooth (0 : X → ℝ) := fun j => contDiffOn_const
  choose CE hCE using fun T => position_tail e X A R Θ hΘ hΘp P C hP T
  have hth : ∀ (T : Finset (Fin e)) i, IsPotential A (if i ∈ T then P i else LocPot.ofFun 0) := by
    intro T i
    split_ifs
    · exact hP i
    · exact isPotential_ofFun A _ hz
  have hph : ∀ (T : Finset (Fin e)) i, A.SmoothOn R.Yo (if i ∈ T then f i else 0) := by
    intro T i
    split_ifs
    · exact hf i
    · exact fun j => contDiffOn_const
  have hsm : ∀ t, (∀ i, A.Smooth (fT i t)) → ∀ (T : Finset (Fin e)) i,
      A.Smooth (if i ∈ T then fT i t else 0) := by
    intro t h T i
    split_ifs
    · exact h i
    · exact hz
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ T : Finset (Fin e),
      (∀ i, A.Smooth (if i ∈ T then fT i t else 0)) ∧
      (∀ i, IsPsh A ((if i ∈ T then P i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then fT i t else 0) + Θ)) ∧
      TailLogBound A R.Yo R.r (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then fT i t else 0) + Θ) (CE T) := by
    filter_upwards [hfT] with t ht T
    have h := hCE T (fun i => fT i t) (fun i => (ht i).1) (fun i => (ht i).2.1)
      (fun i x hx => (ht i).2.2 x hx)
    exact ⟨hsm t (fun i => (ht i).1) T, h.1, h.2⟩
  have hC2 : ∀ (T : Finset (Fin e)) i j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo,
      IsCompact K' → TendstoUniformlyOn
        (fun t => fderiv ℝ (fderiv ℝ ((if i ∈ T then fT i t else 0) ∘ (A.chart j).symm)))
        (fderiv ℝ (fderiv ℝ ((if i ∈ T then f i else 0) ∘ (A.chart j).symm))) (𝓝[>] 0) K' := by
    intro T i j K' hK' hKc
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact (hC i j K' hK' hKc).2.2
    · simp only [hi, if_false]
      exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
        Eventually.of_forall fun t y _ => by simpa using hε
  have term := fun T : Finset (Fin e) => GlobalTheory.T.mixed_integral_regularized_convergence e X A R Θ
    (fun i => if i ∈ T then P i else LocPot.ofFun 0) (fun i => if i ∈ T then f i else 0)
    (fun i t => if i ∈ T then fT i t else 0) G GT C (CE T) hΘ (hth T) (hph T)
    (hev.mono fun t h => h T) (hC2 T) hGT hGc
  refine ⟨?_, ?_, ?_⟩
  · intro j K hK hKc
    letI : MeasurableSpace X := borel X
    haveI : BorelSpace X := ⟨rfl⟩
    have hcl : IsClosed ((A.chart j).symm '' K) :=
      (hKc.image_of_continuousOn ((A.chart j).continuousOn_symm.mono hK)).isClosed
    have hcm : @Measurable X ℝ (borel X) _ (((A.chart j).symm '' K).indicator fun _ => (1 : ℝ)) :=
      measurable_const.indicator hcl.measurableSet
    have hc01 : ∀ x, 0 ≤ ((A.chart j).symm '' K).indicator (fun _ => (1 : ℝ)) x ∧
        ((A.chart j).symm '' K).indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
      intro x
      by_cases hx : x ∈ (A.chart j).symm '' K
      · simp [hx]
      · simp [hx]
    have hcin : ∀ y ∈ K, ((A.chart j).symm '' K).indicator (fun _ => (1 : ℝ)) ((A.chart j).symm y) = 1 :=
      fun y hy => Set.indicator_of_mem (Set.mem_image_of_mem _ hy) _
    have hcout : ∀ y ∈ (A.chart j).target, y ∉ K →
        ((A.chart j).symm '' K).indicator (fun _ => (1 : ℝ)) ((A.chart j).symm y) = 0 := by
      intro y hy hyK
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨y', hy', he⟩
      exact hyK (((A.chart j).symm.injOn (hK hy') hy he) ▸ hy')
    refine (expand_on A R.Yo hYo hnull P f Θ hP hΘ hf j K hKc.measurableSet hK
      (fun y => G ((A.chart j).symm y)) fun T => ?_).1
    have h := (term T j K _ hK hKc hcm hc01 hcout).1
    exact (h.mono_set hK).congr_fun (fun y hy => by simp only [hcin y hy, one_mul]) hKc.measurableSet
  · filter_upwards [hfT, hGT, hev] with t ht hg hevt
    intro j K hK hKc
    refine (expand_on A R.Yo hYo hnull P (fun i => fT i t) Θ hP hΘ
      (fun i k => ((ht i).1 k).mono fun y hy => ⟨hy.1, trivial⟩) j K hKc.measurableSet hK
      (fun y => GT t ((A.chart j).symm y)) fun T => ?_).1
    have hpot : ∀ i, IsPotential A ((if i ∈ T then P i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then fT i t else 0) + Θ) := fun i =>
      isPotentialAdd A _ _ (isPotentialAdd A _ _ (hth T i)
        (isPotential_ofFun A _ ((hevt T).1 i))) hΘ
    exact mIntegrable_of_logBound A R _ (CE T) C (GT t) hpot
      (fun k y hy _ => locDens_nonneg_of_psh A _ hpot (hevt T).2.1 k hy) (hevt T).2.2 hg.1 hg.2
      j K hK hKc
  · have hne : Nonempty (ChartPartition A) := existsPartition A
    simp_rw [mInt_eq_integralWith A _ hne]
    unfold integralWith
    refine tendsto_finset_sum _ fun j _ => ?_
    letI : MeasurableSpace X := borel X
    haveI : BorelSpace X := ⟨rfl⟩
    have hSc : IsCompact ((A.chart j) '' tsupport (hne.some.χ j)) :=
      (isClosed_tsupport _).isCompact.image_of_continuousOn
        ((A.chart j).continuousOn.mono (hne.some.tsupport_subset j))
    have hSt : (A.chart j) '' tsupport (hne.some.χ j) ⊆ (A.chart j).target := by
      rintro _ ⟨x, hx, rfl⟩
      exact (A.chart j).map_source (hne.some.tsupport_subset j hx)
    have hcm : @Measurable X ℝ (borel X) _ (hne.some.χ j) :=
      (ReciprocityTheory.AnForm.M.PLAux.smooth_continuous (hne.some.smooth j)).measurable
    have hc01 : ∀ x, 0 ≤ hne.some.χ j x ∧ hne.some.χ j x ≤ 1 :=
      fun x => ⟨hne.some.nonneg j x, chi_le_one _ j x⟩
    have hcout : ∀ y ∈ (A.chart j).target, y ∉ (A.chart j) '' tsupport (hne.some.χ j) →
        hne.some.χ j ((A.chart j).symm y) = 0 := by
      intro y hy hyS
      have : (A.chart j).symm y ∉ tsupport (hne.some.χ j) := fun h =>
        hyS ⟨_, h, (A.chart j).right_inv hy⟩
      exact image_eq_zero_of_notMem_tsupport this
    have hterm := fun T : Finset (Fin e) => term T j _ _ hSt hSc hcm hc01 hcout
    have hTm := (A.chart j).open_target.measurableSet
    have hlim := (expand_on A R.Yo hYo hnull P f Θ hP hΘ hf j (A.chart j).target hTm subset_rfl
      (fun y => hne.some.χ j ((A.chart j).symm y) * G ((A.chart j).symm y))
      fun T => (hterm T).1).2
    have hfin : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ y in (A.chart j).target,
        hne.some.χ j ((A.chart j).symm y) * GT t ((A.chart j).symm y) *
          locDens A (fun i => P i + LocPot.ofFun (fT i t)) j y =
        ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * ∫ y in (A.chart j).target,
          hne.some.χ j ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i =>
            (if i ∈ T then P i else LocPot.ofFun 0) +
              LocPot.ofFun (if i ∈ T then fT i t else 0) + Θ) j y := by
      filter_upwards [hfT, eventually_all.2 fun T => (hterm T).2.1] with t ht hI
      exact (expand_on A R.Yo hYo hnull P (fun i => fT i t) Θ hP hΘ
        (fun i k => ((ht i).1 k).mono fun y hy => ⟨hy.1, trivial⟩) j (A.chart j).target hTm subset_rfl
        (fun y => hne.some.χ j ((A.chart j).symm y) * GT t ((A.chart j).symm y)) hI).2
    rw [hlim]
    refine Tendsto.congr' (hfin.mono fun t h => h.symm) ?_
    exact tendsto_finset_sum _ fun T _ => ((hterm T).2.2).const_mul _

end GlobalTheory.CompanionTheory.Ar.Giv
