import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

theorem analyticAt_conj_comp_star {e : ℕ} {h : (Fin e → ℂ) → ℂ} {u : Fin e → ℂ}
    (hh : AnalyticAt ℂ h (star u)) :
    AnalyticAt ℂ (fun v => starRingEnd ℂ (h (star v))) u := by
  have hc : ContinuousAt (star : (Fin e → ℂ) → (Fin e → ℂ)) u := continuous_star.continuousAt
  refine GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 ?_
  filter_upwards [hc.eventually hh.eventually_analyticAt] with q hq
  simpa [Function.comp_def] using hq.differentiableAt.star_star

theorem holoOn_conj_comp {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} (c : X → X)
    (hc : Continuous c)
    (hanti : ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z))))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source)))
    {V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) :
    A.HoloOn (c ⁻¹' V) (fun y => starRingEnd ℂ (g (c y))) := by
  intro j w hw
  obtain ⟨k, hk⟩ := A.cover (c ((A.chart j).symm w))
  have hw' : w ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source) := ⟨hw.1, hk⟩
  have h1 := hanti j k w hw'
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) (A.chart k (c ((A.chart j).symm w))) := by
    refine hg k _ ⟨(A.chart k).map_source hk, ?_⟩
    simp only [Set.mem_preimage, (A.chart k).left_inv hk]
    exact hw.2
  have h3 : AnalyticAt ℂ (fun v => starRingEnd ℂ ((g ∘ (A.chart k).symm) (star v)))
      (star (A.chart k (c ((A.chart j).symm w)))) :=
    analyticAt_conj_comp_star (by simpa using h2)
  have h4 := AnalyticAt.comp (g := fun v => starRingEnd ℂ ((g ∘ (A.chart k).symm) (star v)))
    (f := fun z => star (A.chart k (c ((A.chart j).symm z)))) (x := w) h3 h1
  refine h4.congr ?_
  have hcc : ContinuousAt (c ∘ (A.chart j).symm) w :=
    hc.continuousAt.comp ((A.chart j).continuousAt_symm hw.1)
  filter_upwards [hcc ((A.chart k).open_source.mem_nhds hk)] with w' hw''
  have hw3 : c ((A.chart j).symm w') ∈ (A.chart k).source := hw''
  simp [Function.comp, (A.chart k).left_inv hw3]

end GlobalTheory.CompanionTheory.Ar.PB.Cj
