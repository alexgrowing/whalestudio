import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord

theorem holoMap_of_coord : ∀ (e n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas n Y) (pr : X → Y), (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧ ∀ i, B.chart kb (pr x') i = ψ x' (σ i)) → HoloMap A B pr := by
  intro e n X Y _ _ A B pr hloc
  have key : ∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin B.n) (σ : Fin n → Fin e),
      IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∀ x' ∈ ψ.source, pr x' ∈ (B.chart kb).source ∧
        pr x' = (B.chart kb).symm (fun i => ψ x' (σ i)) ∧ (fun i => ψ x' (σ i)) ∈ (B.chart kb).target := by
    intro x
    obtain ⟨ψ, kb, σ, hψ, hx, h⟩ := hloc x
    refine ⟨ψ, kb, σ, hψ, hx, fun x' hx' => ?_⟩
    obtain ⟨hs, hc⟩ := h x' hx'
    have hfun : (fun i => ψ x' (σ i)) = B.chart kb (pr x') := funext fun i => (hc i).symm
    refine ⟨hs, ?_, ?_⟩
    · rw [hfun, (B.chart kb).left_inv hs]
    · rw [hfun]
      exact (B.chart kb).map_source hs
  refine ⟨?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨ψ, kb, σ, -, hx, h⟩ := key x
    let L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
    have hcont : ContinuousOn ((B.chart kb).symm ∘ L ∘ ψ) ψ.source :=
      (B.chart kb).continuousOn_symm.comp (L.continuous.comp_continuousOn ψ.continuousOn)
        (fun x' hx' => (h x' hx').2.2)
    have heq : ((B.chart kb).symm ∘ L ∘ ψ) =ᶠ[𝓝 x] pr :=
      Filter.eventually_of_mem (ψ.open_source.mem_nhds hx) fun x' hx' => ((h x' hx').2.1).symm
    exact (hcont.continuousAt (ψ.open_source.mem_nhds hx)).congr heq
  · intro j k y hy
    obtain ⟨hyt, hys⟩ := hy
    obtain ⟨ψ, kb, σ, hψ, hx, h⟩ := key ((A.chart j).symm y)
    let L : (Fin e → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ i)
    have h1 : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hyt, hx⟩
    have h2 : AnalyticAt ℂ (B.chart k ∘ (B.chart kb).symm) (L (ψ ((A.chart j).symm y))) := by
      apply B.holo kb k
      refine ⟨(h _ hx).2.2, ?_⟩
      show (B.chart kb).symm (fun i => ψ ((A.chart j).symm y) (σ i)) ∈ (B.chart k).source
      rw [← (h _ hx).2.1]
      exact hys
    have h3 : AnalyticAt ℂ ((B.chart k ∘ (B.chart kb).symm) ∘ L ∘ (ψ ∘ (A.chart j).symm)) y :=
      AnalyticAt.comp (f := L ∘ (ψ ∘ (A.chart j).symm)) h2
        (AnalyticAt.comp (f := ψ ∘ (A.chart j).symm) (L.analyticAt _) h1)
    apply h3.congr
    have hnb : ∀ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ ψ.source :=
      (A.chart j).continuousAt_symm hyt (ψ.open_source.mem_nhds hx)
    filter_upwards [hnb] with y' hy'
    simp only [Function.comp_apply]
    rw [(h _ hy').2.1]
    rfl

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord
