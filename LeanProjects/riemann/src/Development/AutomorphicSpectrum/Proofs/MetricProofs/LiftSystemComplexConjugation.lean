import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

open Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_cross {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (k : K) (a b : ι k) :
    z ⟨k, a⟩ * z' ⟨k, b⟩ = z ⟨k, b⟩ * z' ⟨k, a⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  simp only
  ring

theorem sameOrbit_of_cross {z z' : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0)
    (h : ∀ (k : K) (a b : ι k), z ⟨k, a⟩ * z' ⟨k, b⟩ = z ⟨k, b⟩ * z' ⟨k, a⟩) :
    SameOrbit z z' := by
  choose j hj using hz'
  refine ⟨fun k => z ⟨k, j k⟩ / z' ⟨k, j k⟩, fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz k
    refine div_ne_zero (fun h0 => ?_) (hj k)
    have := h k i (j k)
    rw [h0, zero_mul] at this
    exact (mul_ne_zero hi (hj k)) this
  · funext ⟨k, a⟩
    have := h k a (j k)
    have hjk := hj k
    simp only
    field_simp
    linear_combination this

theorem continuousAt_of_holo {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {y : X} (hy : y ∈ U) : ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) y :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm)
      (hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩).continuousAt
      ((A.chart j).continuousAt hj)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [Function.comp, (A.chart j).left_inv hz]

theorem exists_conj_of_isLiftSys {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X}
    {lift : X → X → (Σ k, ι k) → ℂ} (hS : IsLiftSys A P U lift) :
    ∃ c : X → X, (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) ∧ Continuous c ∧
      ∀ x, c (c x) = x := by
  obtain ⟨hU, hmem, hholo, hlift, hcompat, hsurj, hinj, -⟩ := hS
  choose c hc using fun x => hsurj _ (cj_mem_mcPts (hlift x x (hmem x)))
  refine ⟨c, hc, ?_, fun x => ?_⟩
  · refine continuous_iff_ultrafilter.2 fun x F hF => ?_
    obtain ⟨x', -, hx'⟩ := isCompact_univ.ultrafilter_le_nhds (F.map c) (by simp)
    have hcF : Tendsto c F (𝓝 x') := hx'
    have hev : ∀ᶠ y in (F : Filter X), y ∈ U x ∧ c y ∈ U x' :=
      Filter.Eventually.and (hF ((hU x).mem_nhds (hmem x))) (hcF ((hU x').mem_nhds (hmem x')))
    have horb : ∀ᶠ y in (F : Filter X), SameOrbit (lift x' (c y)) (cj (lift x y)) := by
      filter_upwards [hev] with y hy
      exact sameOrbit_trans (hcompat x' (c y) (c y) ⟨hy.2, hmem _⟩)
        (sameOrbit_trans (hc y) (sameOrbit_cj (hcompat y x y ⟨hmem y, hy.1⟩)))
    have hl1 : ∀ p, Tendsto (fun y => lift x' (c y) p) F (𝓝 (lift x' x' p)) := fun p =>
      (continuousAt_of_holo A (hholo x' p) (hmem x')).tendsto.comp hcF
    have hl2 : ∀ p, Tendsto (fun y => cj (lift x y) p) F (𝓝 (cj (lift x x) p)) := fun p =>
      (Complex.continuous_conj.tendsto _).comp
        ((continuousAt_of_holo A (hholo x p) (hmem x)).tendsto.mono_left hF)
    have hcross : ∀ (k : K) (a b : ι k),
        lift x' x' ⟨k, a⟩ * cj (lift x x) ⟨k, b⟩ = lift x' x' ⟨k, b⟩ * cj (lift x x) ⟨k, a⟩ :=
      fun k a b => tendsto_nhds_unique_of_eventuallyEq
        ((hl1 ⟨k, a⟩).mul (hl2 ⟨k, b⟩)) ((hl1 ⟨k, b⟩).mul (hl2 ⟨k, a⟩))
        (horb.mono fun y hy => sameOrbit_cross hy k a b)
    have horb' : SameOrbit (lift x' x') (cj (lift x x)) :=
      sameOrbit_of_cross (hlift x' x' (hmem x')).1 (cj_nonzero (hlift x x (hmem x)).1) hcross
    have hxx : x' = c x := hinj _ _ (sameOrbit_trans horb' (sameOrbit_symm (hc x)))
    exact hxx ▸ hcF
  · refine hinj _ _ (sameOrbit_trans (hc (c x)) ?_)
    have := sameOrbit_cj (hc x)
    rwa [cj_cj] at this

end GlobalTheory.CompanionTheory.Ar.PB.Cj
