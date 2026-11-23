import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

namespace ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

theorem continuousAt_of_chart {e : ℕ} {X : Type} [TopologicalSpace X] {E : Type*}
    [TopologicalSpace E] (A : FinHolAtlas e X) (f : X → E) (y : X) (j : Fin A.n)
    (hy : y ∈ (A.chart j).source) (hf : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j y)) :
    ContinuousAt f y := by
  have h1 := ContinuousAt.comp (x := y) hf ((A.chart j).continuousAt hy)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hy] with z hz
  simp [Function.comp, (A.chart j).left_inv hz]

theorem continuousAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {y : X} (hy : y ∈ U) :
    ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  apply continuousAt_of_chart A g y j hj
  have hmem : (A.chart j) y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm ((A.chart j) y) ∈ U
    rw [(A.chart j).left_inv hj]
    exact hy
  exact (hg j _ hmem).continuousAt

theorem continuousAt_of_smoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U : Set X} (hU : IsOpen U) {g : X → ℝ} (hg : A.SmoothOn U g) {y : X} (hy : y ∈ U) :
    ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  apply continuousAt_of_chart A g y j hj
  have hmem : (A.chart j) y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm ((A.chart j) y) ∈ U
    rw [(A.chart j).left_inv hj]
    exact hy
  exact (hg j).continuousOn.continuousAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hmem)

theorem bdry_iff {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hS : IsSection A L s) {x z : X} (hz : z ∈ L.U x) :
    s z z = 0 ↔ s x z = 0 := by
  have h := hS.2 x z z ⟨hz, L.mem_U z⟩
  have he1 := (Real.exp_pos (-L.φ x z)).ne'
  have he2 := (Real.exp_pos (-L.φ z z)).ne'
  constructor <;> intro h0
  · have h2 : ‖s x z‖ * Real.exp (-L.φ x z) = 0 := by rw [h, h0, norm_zero, zero_mul]
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact norm_eq_zero.1 h1
    · exact absurd h1 he1
  · have h2 : ‖s z z‖ * Real.exp (-L.φ z z) = 0 := by rw [← h, h0, norm_zero, zero_mul]
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact norm_eq_zero.1 h1
    · exact absurd h1 he2

theorem isClosed_bdry {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hS : IsSection A L s) : IsClosed (bdry s) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  have hc : ContinuousAt (s y) y := continuousAt_of_holoOn A (hS.1 y) (L.mem_U y)
  have h1 : ∀ᶠ z in 𝓝 y, s y z ≠ 0 := hc.eventually_ne hy
  filter_upwards [h1, (L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz hzU
  exact fun hb => hz ((bdry_iff hS hzU).1 hb)

theorem interior_bdry_eq_empty {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} {n : ℕ} {m : Fin n → ℕ} {W : Fin n → Set X}
    (hS : IsSection A L s) (hSNC : IsSNC A L s m W) : interior (bdry s) = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  obtain ⟨ψ, -, hyψ, hsrc, σ, -, -, u, -, hu, hfac⟩ := hSNC y
  have hVo : IsOpen (interior (bdry s) ∩ ψ.source) := isOpen_interior.inter ψ.open_source
  have hOo : IsOpen (ψ '' (interior (bdry s) ∩ ψ.source)) := by
    first
    | exact ψ.isOpen_image_of_subset_source hVo Set.inter_subset_right
    | exact ψ.isOpen_image_source_inter isOpen_interior
  have hw0 : ψ y ∈ ψ '' (interior (bdry s) ∩ ψ.source) := ⟨y, ⟨hy, hyψ⟩, rfl⟩

  have hT : Filter.Tendsto (fun t : ℂ => ψ y + t • (fun _ : Fin e => (1 : ℂ))) (𝓝[≠] 0)
      (𝓝 (ψ y)) := by
    have hc : Continuous (fun t : ℂ => ψ y + t • (fun _ : Fin e => (1 : ℂ))) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ψ y + t • (fun _ : Fin e => (1 : ℂ)) ∈
      ψ '' (interior (bdry s) ∩ ψ.source) ∧ ∀ i, ψ y i + t ≠ 0 := by
    refine (hT.eventually (hOo.mem_nhds hw0)).and (Filter.eventually_all.2 fun i => ?_)
    by_cases h0 : ψ y i = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [h0, zero_add]
      exact ht
    · have hc : Continuous (fun t : ℂ => ψ y i + t) := by fun_prop
      have h2 : ∀ᶠ t in 𝓝 (0 : ℂ), ψ y i + t ≠ 0 :=
        hc.continuousAt.eventually_ne (by simpa using h0)
      exact nhdsWithin_le_nhds h2
  obtain ⟨t, ⟨z, ⟨hzI, hzψ⟩, hzt⟩, hne⟩ := hev.exists
  have hzb : z ∈ bdry s := interior_subset hzI
  have hzU : z ∈ L.U y := hsrc hzψ
  have h1 : s y z = 0 := (bdry_iff hS hzU).1 hzb
  rw [hfac z hzψ] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact hu z hzψ h2
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h2
    rcases hσ : σ k with _ | i
    · simp [hσ] at hk
    · simp only [hσ] at hk
      have hzi : ψ z i = ψ y i + t := by
        rw [hzt]
        simp
      exact hne i (by rw [← hzi]; by_contra hz0; exact pow_ne_zero _ hz0 hk)

theorem levi_sub_const {D : ℕ} (f : (Fin D → ℂ) → ℝ) (a : ℝ) (z w : Fin D → ℂ) :
    levi (fun y => f y - a) z w = levi f z w := by
  unfold levi
  rw [show fderiv ℝ (fun y => f y - a) = fderiv ℝ f from funext fun _ => fderiv_sub_const a]

end

end ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology
