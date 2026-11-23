import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisorStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralModelFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem continuous_of_atlasSmooth {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    have := (hf j).continuousOn
    simpa [Set.preimage_univ, Set.inter_univ] using this
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    (h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp
      ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

theorem tendsto_ptsIntegral_of_chart_conv : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (Θ : LocPot M.Xc) (Pp : Fin n → LocPot M.Xc) (f : Fin n → M.Xc → ℝ) (fT : Fin n → ℝ → M.Xc → ℝ) (G : M.Xc → ℝ) (GT : ℝ → M.Xc → ℝ) (C : ℝ) (L : ℝ → Fin n → HermLine ι) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ), IsArithVar P (n + 1) → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → (∀ i, IsPotential M.atlas (Pp i)) → (∀ i, M.atlas.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, M.atlas.Smooth (fT i t) ∧ IsPsh M.atlas (Pp i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (M.atlas.chart j).symm) (f i ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (f i ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (GT t) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i x, ∀ y₀ ∈ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G' : M.Xc → ℂ, M.atlas.HoloOn U G' ∧ ∀ y' ∈ U, (Pp i + LocPot.ofFun (fT i t)).φ x y' - Real.log ((L t i).h (s y')) = (G' y').re) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ mcPts P, g t z = GT t (M.proj z)) → ∃ l : ℝ, Tendsto (fun t => ptsIntegral P (pot (L t)) (g t)) (𝓝[>] 0) (𝓝 l) := by
  intro K _ ι _ P n M R Θ Pp f fT G GT C L g hV hΘ hΘp hP hf hfT hconv hGT hGc hrel hg
  classical
  by_cases hQ : ∃ Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj P Q
  · have hYo := (GlobalTheory.T.regular_chart_data_properties n M.Xc M.atlas R).1
    have hmeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable M.Xc ℝ (borel M.Xc) _ (R.Yo.indicator (GT t)) ∧
        ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x) := by
      filter_upwards [hGT] with t ht
      refine ⟨?_, ht.2⟩
      letI : MeasurableSpace M.Xc := borel M.Xc
      haveI : BorelSpace M.Xc := ⟨rfl⟩
      exact (continuous_of_atlasSmooth ht.1).measurable.indicator hYo.measurableSet
    obtain ⟨-, hint, hlim⟩ := GlobalTheory.T.mixed_integral_tendsto_off_divisor n M.Xc M.atlas R Θ hΘ hΘp Pp f fT G GT C hP hf hfT hconv
      hmeas hGc
    refine ⟨_, hlim.congr' ?_⟩
    filter_upwards [hint, hfT, hGT, hrel, hg] with t hit hft hgt hrt hgt'
    have hpush := GlobalTheory.T.mixed_integral_model_formula K ι P n M hQ.choose Set.univ ∅ ∅ (fun _ => 1) (L t)
      (fun i => Pp i + LocPot.ofFun (fT i t)) (g t) (GT t) hV hQ.choose_spec isOpen_univ
      (fun j => by simp)
      (fun Ψ _ => by simp)
      (fun i x => by
        intro j
        have h1 := (hP i).1 x j
        have h2 := (hft i).1 j
        have h3 := h1.add (h2.mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩))
        refine (h3.mono ?_).congr ?_
        · rintro y ⟨hy, hy'⟩
          exact ⟨hy, hy'.1.1⟩
        · intro y _
          rfl)
      (fun i x y₀ hy₀ => by
        obtain ⟨U, hU, hyU, hUs, s, hs, hsp, G', hG', hrel'⟩ := hrt i x y₀ hy₀
        exact ⟨U, hU, hyU, hUs, s, hs, hsp, G', hG', fun y' hy' => by
          simpa using hrel' y' hy'⟩)
      (fun z hz _ _ _ => hgt' z hz)
      (fun j => ((continuous_of_atlasSmooth hgt.1).comp_continuousOn
        (M.atlas.chart j).continuousOn_symm).aestronglyMeasurable (M.atlas.chart j).open_target.measurableSet)
    have h3 := (hpush.2.2 hit).2
    have hpot : (fun i z => (fun _ : Fin n => (1 : ℝ)) i * Real.log ((L t i).h z)) = pot (L t) := by
      funext i z
      simp [pot]
    rw [hpot] at h3
    rw [ptsIntegral, dif_pos hQ, h3]
  · refine ⟨0, ?_⟩
    have : (fun t => ptsIntegral P (pot (L t)) (g t)) = fun _ => (0 : ℝ) := by
      funext t
      rw [ptsIntegral, dif_neg hQ]
    rw [this]
    exact tendsto_const_nhds

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
