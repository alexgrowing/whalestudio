import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalc

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem isCoveringMapOn_of_proper {n : ℕ} {E : Type*} [TopologicalSpace E] [T2Space E] (z : E → V n)
    (U : Set (V n)) (hU : IsOpen U) (hz : ∀ x, z x ∈ U) (hl : IsLocalHomeomorph z)
    (hp : ∀ K : Set (V n), IsCompact K → K ⊆ U → IsCompact (z ⁻¹' K)) :
    IsCoveringMapOn z U ∧ ∀ y, (z ⁻¹' {y}).Finite := by
  let g : E → U := fun x => ⟨z x, hz x⟩
  have hgc : Continuous g := hl.continuous.subtype_mk _
  have hgl : IsLocalHomeomorph g :=
    IsLocalHomeomorph.of_comp (g := Subtype.val) (by simpa [Function.comp_def, g] using hl)
      hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph hgc
  have hgp : IsProperMap g := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hgc, fun K hK => ?_⟩
    have h1 := hp (Subtype.val '' K) (hK.image continuous_subtype_val)
      (by rintro _ ⟨y, -, rfl⟩; exact y.2)
    have h2 : g ⁻¹' K = z ⁻¹' (Subtype.val '' K) := by
      ext x; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx; exact ⟨g x, hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = g x := Subtype.ext hyx
        rw [← this]; exact hy
    rw [h2]; exact h1
  have hfib : ∀ y (hy : y ∈ U), (z ⁻¹' {y}).Finite := by
    intro y hy
    have h2 : z ⁻¹' {y} = g ⁻¹' {⟨y, hy⟩} := by
      ext x; simp [g, Subtype.ext_iff]
    rw [h2]
    refine (hgp.isCompact_preimage isCompact_singleton).finite ?_
    refine (hgl.isLocalHomeomorphOn.mono (Set.subset_univ _)).isDiscrete_of_image ?_
    refine (Set.subsingleton_singleton.anti (Set.image_preimage_subset _ _)).isDiscrete
  refine ⟨?_, fun y => ?_⟩
  · refine IsCoveringMapOn.of_isCoveringMap_subtype hU hz ?_
    refine isCoveringMap_iff_isCoveringMapOn_univ.2 ?_
    refine hgp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => ?_)
      hgl.isLocalHomeomorphOn
    have h2 : g ⁻¹' {x} = z ⁻¹' {(x : V n)} := by
      ext x'; simp [g, Subtype.ext_iff]
    rw [h2]; exact hfib x x.2
  · by_cases hy : y ∈ U
    · exact hfib y hy
    · convert Set.finite_empty
      ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h; exact hy (h ▸ hz x)

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem transition_zero_eq_one (A : WeightedAtlas n Y ι La) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) : A.g 0 i j y = 1 := by
  have h := A.g_add 0 0 i j y hi hj
  rw [add_zero] at h
  have hne := A.g_ne 0 i j y hi hj
  exact mul_left_cancel₀ hne ((h.symm).trans (mul_one _).symm)

theorem transition_nsmul_eq_pow (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    A.g (m • la) i j y = A.g la i j y ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, transition_zero_eq_one A i j y hi hj]
  | succ k ih => rw [succ_nsmul, A.g_add _ _ i j y hi hj, ih, pow_succ]

theorem weight_zero_eq_zero (A : WeightedAtlas n Y ι La) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) : A.ph 0 i y = 0 := by
  have h := A.ph_add 0 0 i y hi
  rw [add_zero] at h
  linarith

theorem weight_nsmul_eq_mul (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) : A.ph (m • la) i y = m * A.ph la i y := by
  induction m with
  | zero => rw [zero_nsmul, weight_zero_eq_zero A i y hi]; simp
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hi, ih]; push_cast; ring

theorem ratio_pow_chart_independent (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (F w0 : ι → Y → ℂ)
    (hF : A.IsSec (m • la) F) (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    F i y / w0 i y ^ m = F j y / w0 j y ^ m := by
  rw [hF.2 i j y (Set.mem_univ y) hi hj, hw.2 i j y (Set.mem_univ y) hi hj,
    transition_nsmul_eq_pow A la m i j y hi hj, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (A.g_ne la i j y hi hj))

theorem ne_zero_of_overlap_ne_zero (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) (h : w0 j y ≠ 0) :
    w0 i y ≠ 0 := by
  rw [hw.2 i j y (Set.mem_univ y) hi hj]
  exact mul_ne_zero (A.g_ne la i j y hi hj) h

theorem localCoordinates_eq_zmap (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) :
    A.zLoc w0 s i (A.chart i y) = A.zmap w0 s y := by
  simp only [zLoc, zmap, (A.chart i).left_inv hi]
  congr 1
  funext k
  have := ratio_pow_chart_independent A la 1 (s k) w0 (by rw [one_nsmul]; exact hs k) hw i (A.pick y) y hi
    (A.mem_pick y)
  simpa using this

end atlas

theorem holo_restrict_open {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n) (u : M → ℂ)
    (hu : Holo n z u) (S : Set M) (hS : IsOpen S) [Nonempty S] :
    Holo n (fun x : S => z x) (fun x : S => u x) := by
  intro e he
  let f := hS.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : S → M)
  have hc : IsChart n z (f.symm.trans e) := by
    intro x hx
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage, f, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hx
    obtain ⟨⟨x', rfl⟩, hx2⟩ := hx
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, f,
      hS.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv] at hx2 ⊢
    exact he hx2
  have h2 := hu _ hc
  have ht : (f.symm.trans e).target = e.target := by
    simp [f]
  rw [ht] at h2
  refine h2.congr (fun v hv => ?_)
  simp [f, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

theorem sub_isBigO_of_det_ne_zero {n : ℕ} {q : V n → V n} {D : V n →L[ℂ] V n} {a : V n}
    (hq : HasFDerivAt q D a) (hD : LinearMap.det (D : V n →ₗ[ℂ] V n) ≠ 0) :
    (fun x => x - a) =O[𝓝 a] (fun x => q x - q a) := by
  let E : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (D : V n →ₗ[ℂ] V n) hD).toContinuousLinearEquiv
  have hE : ∀ x, E x = D x := by
    intro x
    rfl
  have h1 : (fun x => x - a) =O[𝓝 a] (fun x => D (x - a)) := by
    simpa [hE] using E.isBigO_sub_rev (𝓝 a) a
  have h3 : (fun x => D (x - a) - (q x - q a)) =o[𝓝 a] (fun x => D (x - a)) := by
    have := (hq.isLittleO.trans_isBigO h1).neg_left
    refine this.congr_left (fun x => ?_)
    abel
  have h4 := h3.right_isBigO_sub
  refine h1.trans (h4.congr_right (fun x => ?_))
  abel

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem differentiableAt_localCoordinates (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (h0 : w0 i y ≠ 0) :
    DifferentiableAt ℂ (A.zLoc w0 s i) (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hd : ∀ F : ι → Y → ℂ, A.IsSec la F →
      DifferentiableAt ℂ (fun v => F i ((A.chart i).symm v)) (A.chart i y) := by
    intro F hF
    have := hF.1 i
    simp only [Set.preimage_univ, Set.inter_univ] at this
    exact (this.differentiableAt hT)
  rw [differentiableAt_euclidean]
  intro k
  simp only [zLoc, PiLp.toLp_apply, div_eq_mul_inv]
  refine (hd (s k) (hs k)).mul ((hd w0 hw).inv ?_)
  simpa [(A.chart i).left_inv hi] using h0

end atlas

end

end ReciprocityTheory.L2DbarEstimates.Y
