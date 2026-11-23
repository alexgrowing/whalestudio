import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem isOpen_ovl (j i : ι) : IsOpen (ovl A.chart j i) :=
  (A.chart j).isOpen_inter_preimage_symm (A.chart i).open_source

theorem trans_contDiffOn (j i : ι) :
    ContDiffOn ℂ ∞ ((A.chart i) ∘ (A.chart j).symm) (ovl A.chart j i) := by
  refine contDiffOn_piLp' 2 fun k => ?_
  have h : DifferentiableOn ℂ (fun x => ((A.chart i) ((A.chart j).symm x)) k) (ovl A.chart j i) :=
    (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn (A.holo_trans j i)
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.isOpen_ovl j i) h

def chiC (i : ι) (β : V n → ℝ) (y : Y) : ℝ :=
  open Classical in if y ∈ (A.chart i).source then β (A.chart i y) else 0

theorem chiC_of_mem {i : ι} {β : V n → ℝ} {y : Y} (hy : y ∈ (A.chart i).source) :
    A.chiC i β y = β (A.chart i y) := by simp [chiC, hy]

theorem chiC_eq_zero {i : ι} {β : V n → ℝ} {K0 : Set (V n)} (hβs : ∀ u, β u ≠ 0 → u ∈ K0)
    {y : Y} (hy : y ∉ (A.chart i).symm '' K0) : A.chiC i β y = 0 := by
  unfold chiC
  split_ifs with h
  · by_contra hne
    exact hy ⟨_, hβs _ hne, (A.chart i).left_inv h⟩
  · rfl

theorem isCompact_chartImage {i : ι} {K0 : Set (V n)} (hK0 : IsCompact K0)
    (hK0t : K0 ⊆ (A.chart i).target) : IsCompact ((A.chart i).symm '' K0) :=
  hK0.image_of_continuousOn ((A.chart i).continuousOn_symm.mono hK0t)

theorem chartImage_subset {i : ι} {K0 : Set (V n)} (hK0t : K0 ⊆ (A.chart i).target) :
    (A.chart i).symm '' K0 ⊆ (A.chart i).source := by
  rintro _ ⟨u, hu, rfl⟩; exact (A.chart i).map_target (hK0t hu)

theorem chiC_smooth {i : ι} {β : V n → ℝ} (hβ : ContDiff ℝ ∞ β) {K0 : Set (V n)}
    (hβs : ∀ u, β u ≠ 0 → u ∈ K0) (hK0 : IsCompact K0) (hK0t : K0 ⊆ (A.chart i).target) :
    A.SmoothFn (A.chiC i β) := by
  intro j
  refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
  by_cases hx : (A.chart j).symm v ∈ (A.chart i).source
  · refine ⟨ovl A.chart j i, A.isOpen_ovl j i, ⟨hv, hx⟩, ?_⟩
    refine (hβ.comp_contDiffOn (((A.trans_contDiffOn j i).restrict_scalars ℝ).mono
      Set.inter_subset_right)).congr fun v' hv' => ?_
    simp only [Function.comp]
    exact A.chiC_of_mem hv'.2.2
  · have hKc := (A.isCompact_chartImage hK0 hK0t).isClosed
    have hxK : (A.chart j).symm v ∉ (A.chart i).symm '' K0 :=
      fun h => hx (A.chartImage_subset hK0t h)
    refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' ((A.chart i).symm '' K0)ᶜ,
      (A.chart j).isOpen_inter_preimage_symm hKc.isOpen_compl, ⟨hv, hxK⟩, ?_⟩
    refine (contDiffOn_const (c := (0 : ℝ))).congr fun v' hv' => ?_
    simp only [Function.comp]
    exact A.chiC_eq_zero hβs hv'.2.2

def F0 (la' : La) (Sf : Finset Y) (idx : Y → ι) (χ : Y → Y → ℝ) (c : Y → ℂ) (j : ι) (y : Y) : ℂ :=
  ∑ P ∈ Sf, c P * (χ P y : ℂ) * A.g la' j (idx P) y

theorem isSmoothSection_localizedSection (la' : La) (Sf : Finset Y) (idx : Y → ι) (χ : Y → Y → ℝ) (c : Y → ℂ)
    (K : Y → Set Y) (hχ : ∀ P ∈ Sf, A.SmoothFn (χ P)) (hχs : ∀ P ∈ Sf, ∀ y, χ P y ≠ 0 → y ∈ K P)
    (hKc : ∀ P ∈ Sf, IsCompact (K P)) (hKs : ∀ P ∈ Sf, K P ⊆ (A.chart (idx P)).source) :
    A.IsSSec la' (A.F0 la' Sf idx χ c) := by
  refine ⟨fun j => ?_, fun i j y hi hj => ?_⟩
  · have : (A.F0 la' Sf idx χ c j ∘ (A.chart j).symm) = fun v => ∑ P ∈ Sf,
        c P * (χ P ((A.chart j).symm v) : ℂ) * A.g la' j (idx P) ((A.chart j).symm v) := by
      funext v; rfl
    rw [this]
    refine ContDiffOn.sum fun P hP => contDiffOn_of_locally_contDiffOn fun v hv => ?_
    by_cases hx : (A.chart j).symm v ∈ (A.chart (idx P)).source
    · refine ⟨ovl A.chart j (idx P), A.isOpen_ovl j _, ⟨hv, hx⟩, ?_⟩
      have hg : ContDiffOn ℝ ∞ (A.g la' j (idx P) ∘ (A.chart j).symm) (ovl A.chart j (idx P)) :=
        contDiffOn_of_holo (A.isOpen_ovl j _) (A.holo_g la' j (idx P))
      have hc : ContDiffOn ℝ ∞ (fun v => (χ P ((A.chart j).symm v) : ℂ)) (A.chart j).target :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ P hP j)
      exact ((contDiffOn_const.mul hc).mono Set.inter_subset_left).mul
        (hg.mono Set.inter_subset_right)
    · have hKc' := (hKc P hP).isClosed
      have hxK : (A.chart j).symm v ∉ K P := fun h => hx (hKs P hP h)
      refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' (K P)ᶜ,
        (A.chart j).isOpen_inter_preimage_symm hKc'.isOpen_compl, ⟨hv, hxK⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℂ))).congr fun v' hv' => ?_
      have h0 : χ P ((A.chart j).symm v') = 0 := by
        by_contra h; exact hv'.2.2 (hχs P hP _ h)
      simp [h0]
  · unfold F0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    by_cases hy : y ∈ (A.chart (idx P)).source
    · rw [A.g_cocycle la' i j (idx P) y hi hj hy]; ring
    · have h0 : χ P y = 0 := by by_contra h; exact hy (hKs P hP (hχs P hP y h))
      simp [h0]

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
