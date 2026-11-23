import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DominatedConvergenceExhaustionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailLogBoundLocalIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvDensOfOpen
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensAddOfFunContinuousOn
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem tendsto_logPow_div_exp_add (CE : ℝ) (e : ℕ) :
    Tendsto (fun n : ℕ => CE * Real.log (Real.exp 1 + n) ^ (e + 1) / (Real.exp 1 + n)) atTop (𝓝 0) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := e + 1)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun n : ℕ => Real.exp 1 + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have h3 := (h.comp h2).const_mul CE
  simpa [mul_div_assoc] using h3

theorem tendstoUniformlyOn_cutoff_comp {β X : Type*} (σ : β → X) (c : X → ℝ)
    (hc : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (F : ℝ → X → ℝ) (f : X → ℝ) (l : Filter ℝ) (K : Set X)
    (E : Set β) (hE : ∀ y ∈ E, σ y ∈ K) (h : TendstoUniformlyOn F f l K) :
    TendstoUniformlyOn (fun t y => c (σ y) * F t (σ y)) (fun y => c (σ y) * f (σ y)) l E := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with t ht y hy
  have h1 := ht (σ y) (hE y hy)
  rw [Real.dist_eq] at h1 ⊢
  calc |c (σ y) * f (σ y) - c (σ y) * F t (σ y)|
      = c (σ y) * |f (σ y) - F t (σ y)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (hc _).1]
    _ ≤ 1 * |f (σ y) - F t (σ y)| := mul_le_mul_of_nonneg_right (hc _).2 (abs_nonneg _)
    _ < ε := by simpa using h1

theorem integrableOn_compl_of_ae_eq_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (E : Set α) (hE : MeasurableSet E) (f T : α → ℝ) (b : ℝ) (hT : Integrable T μ)
    (hT0 : ∀ᵐ y ∂μ, 0 ≤ T y) (hb : ∫ y, T y ∂μ ≤ b) (heq : ∀ᵐ y ∂μ, y ∉ E → f y = T y) :
    IntegrableOn f Eᶜ μ ∧ ∫ y in Eᶜ, f y ∂μ ≤ b := by
  have h : f =ᵐ[μ.restrict Eᶜ] T := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hE.compl]
    filter_upwards [heq] with y hy hyE using hy hyE
  refine ⟨(hT.integrableOn (s := Eᶜ)).congr h.symm, ?_⟩
  rw [integral_congr_ae h]
  exact (setIntegral_le_integral hT hT0).trans hb

theorem conv_chart_integral : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (G : X → ℝ) (GT : ℝ → X → ℝ) (C CE : ℝ), IsPotential A Θ → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn R.Yo (ph i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (phT i t)) ∧ (∀ i, IsPsh A (th i + LocPot.ofFun (phT i t) + Θ)) ∧ GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => th i + LocPot.ofFun (phT i t) + Θ) CE) → (∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT i t ∘ (A.chart j).symm))) (fderiv ℝ (fderiv ℝ (ph i ∘ (A.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable X ℝ (borel X) _ (R.Yo.indicator (GT t)) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → ∀ (j : Fin A.n) (S : Set (Fin e → ℂ)) (c : X → ℝ), S ⊆ (A.chart j).target → IsCompact S → @Measurable X ℝ (borel X) _ c → (∀ x, 0 ≤ c x ∧ c x ≤ 1) → (∀ y ∈ (A.chart j).target, y ∉ S → c ((A.chart j).symm y) = 0) → IntegrableOn (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y) (A.chart j).target ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IntegrableOn (fun y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (A.chart j).target) ∧ Tendsto (fun t => ∫ y in (A.chart j).target, c ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (𝓝[>] 0) (𝓝 (∫ y in (A.chart j).target, c ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y)) := by
  intro e X _ _ _ A R Θ th ph phT G GT C CE hΘ hth hph hev hconv hGev hGconv j S c hST hS hcm hc01 hc0
  obtain ⟨hYo, hnull, -, hKc⟩ := GlobalTheory.T.regular_chart_data_properties e X A R
  have hsymmS : ContinuousOn (A.chart j).symm S := (A.chart j).continuousOn_symm.mono hST
  have hSm : MeasurableSet S := hS.measurableSet
  have hTm : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → Set (Fin e → ℂ), ∀ n, E n = S ∩ (A.chart j).symm ⁻¹'
      {x | x ∈ R.Yo ∧ R.r x ≤ Real.exp 1 + n} := ⟨_, fun _ => rfl⟩
  have hEmem : ∀ n y, y ∈ E n ↔ y ∈ S ∧ (A.chart j).symm y ∈ R.Yo ∧
      R.r ((A.chart j).symm y) ≤ Real.exp 1 + n := by
    intro n y; rw [hEdef]; rfl
  have hEc : ∀ n, IsCompact (E n) := by
    intro n; rw [hEdef]
    exact hS.of_isClosed_subset
      (hsymmS.preimage_isClosed_of_isClosed hS.isClosed (hKc _).isClosed) Set.inter_subset_left
  have hEsub : ∀ n, E n ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo := fun n y hy => by
    have := (hEmem n y).1 hy
    exact ⟨hST this.1, this.2.1⟩
  have hEm : ∀ n, MeasurableSet (E n) := fun n => (hEc n).measurableSet
  have hEmono : Monotone E := by
    intro m n hmn y hy
    obtain ⟨h1, h2, h3⟩ := (hEmem m y).1 hy
    refine (hEmem n y).2 ⟨h1, h2, h3.trans ?_⟩
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hEfin : ∀ n, (volume.restrict S) (E n) < ⊤ := fun n => by
    rw [Measure.restrict_apply (hEm n)]
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) (hEc n).measure_lt_top
  have hae : ∀ᵐ y ∂(volume.restrict S), y ∈ S ∧ (A.chart j).symm y ∈ R.Yo := by
    rw [ae_restrict_iff' hSm]
    filter_upwards [compl_mem_ae_iff.2 (hnull j)] with y hy hyS
    refine ⟨hyS, ?_⟩
    by_contra h
    exact hy ⟨hST hyS, h⟩
  have hex : ∀ᵐ y ∂(volume.restrict S), ∃ n, y ∈ E n := by
    filter_upwards [hae] with y hy
    obtain ⟨n, hn⟩ := exists_nat_ge (R.r ((A.chart j).symm y))
    refine ⟨n, (hEmem n y).2 ⟨hy.1, hy.2, ?_⟩⟩
    have := Real.exp_pos 1
    linarith
  have hlog : ∀ x ∈ R.Yo, 0 ≤ Real.log (R.r x) := fun x hx => Real.log_nonneg (R.one_le_r x hx)
  have hL : ∀ᵐ y ∂(volume.restrict S), 0 ≤ Real.log (R.r ((A.chart j).symm y)) := by
    filter_upwards [hae] with y hy using hlog _ hy.2
  have hGbd : ∀ n : ℕ, ∃ M : ℝ, ∀ x, x ∈ R.Yo → R.r x ≤ Real.exp 1 + n → |G x| ≤ M := by
    intro n
    have hu := hGconv _ (fun x hx => hx.1) (hKc (Real.exp 1 + n))
    have h1 := Metric.tendstoUniformlyOn_iff.1 hu 1 one_pos
    obtain ⟨t, ht1, ht2⟩ := (h1.and hGev).exists
    refine ⟨1 + (|C| + |C| * Real.log (Real.exp 1 + n)), fun x hx hxr => ?_⟩
    have a1 := ht1 x ⟨hx, hxr⟩
    have a2 := ht2.2 x hx
    have a3 : Real.log (R.r x) ≤ Real.log (Real.exp 1 + n) :=
      Real.log_le_log (by linarith [R.one_le_r x hx]) hxr
    have a4 := hlog x hx
    rw [Real.dist_eq] at a1
    have a5 := abs_sub_abs_le_abs_sub (G x) (GT t x)
    have a6 : C * Real.log (R.r x) ≤ |C| * Real.log (R.r x) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) a4
    have a7 : |C| * Real.log (R.r x) ≤ |C| * Real.log (Real.exp 1 + n) :=
      mul_le_mul_of_nonneg_left a3 (abs_nonneg C)
    have a8 := le_abs_self C
    linarith
  have hρ : ∀ n, TendstoUniformlyOn (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
      (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j) (𝓝[>] 0) (E n) := fun n =>
    GlobalTheory.CompanionTheory.Ar.Giv.conv_dens_of_open A Θ R.Yo th ph phT hYo hΘ hth hph
      (hev.mono fun t h => h.1) hconv j (E n) (hEsub n) (hEc n)
  have hΓ : ∀ n, TendstoUniformlyOn
      (fun t y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y))
      (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y)) (𝓝[>] 0) (E n) := fun n =>
    tendstoUniformlyOn_cutoff_comp (A.chart j).symm c hc01 GT G _ {x | x ∈ R.Yo ∧ R.r x ≤ Real.exp 1 + n} (E n)
      (fun y hy => ⟨((hEmem n y).1 hy).2.1, ((hEmem n y).1 hy).2.2⟩)
      (hGconv _ (fun x hx => hx.1) (hKc (Real.exp 1 + n)))
  have hM : ∀ n, ∃ M : ℝ, ∀ y ∈ E n,
      |locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y| ≤ M ∧
      |c ((A.chart j).symm y) * G ((A.chart j).symm y)| ≤ M := by
    intro n
    obtain ⟨M1, h1⟩ := (hEc n).exists_bound_of_continuousOn
      ((GlobalTheory.CompanionTheory.Ar.Giv.locDens_add_ofFun_continuousOn A R.Yo th ph Θ hYo hth hΘ hph j).mono (hEsub n))
    obtain ⟨M2, h2⟩ := hGbd n
    refine ⟨max M1 M2, fun y hy => ⟨(h1 y hy).trans (le_max_left _ _), ?_⟩⟩
    obtain ⟨-, b2, b3⟩ := (hEmem n y).1 hy
    rw [abs_mul, abs_of_nonneg (hc01 _).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hc01 _).2).trans ((h2 _ b2 b3).trans (le_max_right _ _))
  have hEv : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j) (volume.restrict S) ∧
      AEStronglyMeasurable (fun y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y)) (volume.restrict S) ∧
      (∀ᵐ y ∂(volume.restrict S), 0 ≤ locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) ∧
      (∀ᵐ y ∂(volume.restrict S), y ∉ E 0 →
        |c ((A.chart j).symm y) * GT t ((A.chart j).symm y)| ≤ 2 * |C| * Real.log (R.r ((A.chart j).symm y))) ∧
      ∀ n, IntegrableOn (fun y => Real.log (R.r ((A.chart j).symm y)) *
          locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (E n)ᶜ (volume.restrict S) ∧
        ∫ y in (E n)ᶜ, Real.log (R.r ((A.chart j).symm y)) *
          locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y ∂(volume.restrict S) ≤
          CE * Real.log (Real.exp 1 + n) ^ (e + 1) / (Real.exp 1 + n) := by
    filter_upwards [hev, hGev] with t ⟨hs, hp, ht⟩ ⟨hm, hb⟩
    have hpot : ∀ i, IsPotential A (th i + LocPot.ofFun (phT i t) + Θ) := fun i =>
      isPotentialAdd A _ _ (isPotentialAdd A _ _ (hth i) (isPotential_ofFun A _ (hs i))) hΘ
    have hnn : ∀ y ∈ (A.chart j).target,
        0 ≤ locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y :=
      fun y hy => locDens_nonneg_of_psh A _ hpot hp j hy
    have htail := fun n : ℕ => GlobalTheory.T.tail_log_bound_local_integrable A R.Yo R.r _ CE hpot R.one_le_r
      (fun j' y hy _ => locDens_nonneg_of_psh A _ hpot hp j' hy) ht j S hST hS
      (Real.exp 1 + n) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
                           linarith)
    refine ⟨((locDensCont A _ hpot j).mono hST).aestronglyMeasurable hSm, ?_, ?_, ?_, ?_⟩
    · letI : MeasurableSpace X := borel X
      haveI : BorelSpace X := ⟨rfl⟩
      have h1 : AEMeasurable (A.chart j).symm (volume.restrict S) := hsymmS.aemeasurable hSm
      have h2 : AEMeasurable (fun y => c ((A.chart j).symm y) *
          R.Yo.indicator (GT t) ((A.chart j).symm y)) (volume.restrict S) :=
        (hcm.comp_aemeasurable h1).mul (hm.comp_aemeasurable h1)
      refine h2.aestronglyMeasurable.congr ?_
      filter_upwards [hae] with y hy
      rw [Set.indicator_of_mem hy.2]
    · filter_upwards [hae] with y hy using hnn y (hST hy.1)
    · filter_upwards [hae] with y hy hyE
      have hr : Real.exp 1 < R.r ((A.chart j).symm y) := by
        by_contra h
        exact hyE ((hEmem 0 y).2 ⟨hy.1, hy.2, by simpa using not_lt.1 h⟩)
      have hl : 1 ≤ Real.log (R.r ((A.chart j).symm y)) := by
        rw [Real.le_log_iff_exp_le (lt_trans (Real.exp_pos 1) hr)]
        exact hr.le
      have b1 := hb _ hy.2
      have b2 : C * Real.log (R.r ((A.chart j).symm y)) ≤
          |C| * Real.log (R.r ((A.chart j).symm y)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
      have b3 : |C| * 1 ≤ |C| * Real.log (R.r ((A.chart j).symm y)) :=
        mul_le_mul_of_nonneg_left hl (abs_nonneg C)
      have b4 := le_abs_self C
      rw [abs_mul, abs_of_nonneg (hc01 _).1]
      have b5 := mul_le_of_le_one_left (abs_nonneg (GT t ((A.chart j).symm y))) (hc01 ((A.chart j).symm y)).2
      linarith
    · intro n
      refine integrableOn_compl_of_ae_eq_nonneg _ (E n) (hEm n) _ _ _ (htail n).1 ?_ (htail n).2 ?_
      · filter_upwards [hae] with y hy
        exact mul_nonneg (Set.indicator_nonneg (fun x hx => hlog x hx.1) _) (hnn y (hST hy.1))
      · filter_upwards [hae] with y hy hyE
        have hmem : (A.chart j).symm y ∈
            GroundTheory.Heights₂.Heights.AnalyticLimit.tail R.Yo R.r (Real.exp 1 + n) := by
          refine ⟨hy.2, ?_⟩
          by_contra h
          exact hyE ((hEmem n y).2 ⟨hy.1, hy.2, (not_le.1 h).le⟩)
        rw [Set.indicator_of_mem hmem]
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.dominated_convergence_exhaustion (volume.restrict S) (𝓝[>] (0 : ℝ)) E
    (fun y => Real.log (R.r ((A.chart j).symm y)))
    (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
    (fun t y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y))
    (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j)
    (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y))
    (2 * |C|) (fun n => CE * Real.log (Real.exp 1 + n) ^ (e + 1) / (Real.exp 1 + n))
    hEm hEmono hEfin hex hL (by positivity) (tendsto_logPow_div_exp_add CE e) hρ hΓ hM hEv
  have e1 : ∀ (g : X → ℝ) (d : (Fin e → ℂ) → ℝ),
      ∫ y in (A.chart j).target, c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y =
      ∫ y in S, c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y := fun g d =>
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hTm hST
      (fun y hy => by simp [hc0 y hy.1 hy.2])
  have e2 : ∀ (g : X → ℝ) (d : (Fin e → ℂ) → ℝ),
      Integrable (fun y => c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y) (volume.restrict S) →
      IntegrableOn (fun y => c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y) (A.chart j).target :=
    fun g d h => IntegrableOn.of_forall_diff_eq_zero h hTm
      (fun y hy => by simp [hc0 y hy.1 hy.2])
  refine ⟨e2 _ _ i1, i2.mono fun t h => e2 _ _ h, ?_⟩
  rw [e1 G]
  exact Tendsto.congr (fun t => (e1 (GT t) _).symm) i3

end GlobalTheory.CompanionTheory.Ar.Giv
