import ReciprocityTheory.L2DbarEstimates.LeviForms.ApplyA

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff Classical

theorem ap_gt_eq_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (c : M → ℂ) (W : M → Set M) (hS : (zeroSet n g).Finite) (y : M) :
    gt n z g c W y = ∑ p ∈ hS.toFinset, (W p).indicator (fun y => c p * jac n z g y) y := by
  unfold gt
  exact finsum_mem_eq_finite_toFinset_sum _ hS

theorem ap_gt_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (hS : (zeroSet n g).Finite)
    (hW : IsLocalData n g ph r W m) (x : M) (hx : ev n g ph r x < m) :
    gt n z g c W =ᶠ[𝓝 x]
      fun y => (∑ p ∈ hS.toFinset, if x ∈ W p then c p else 0) * jac n z g y := by
  have key : ∀ p ∈ hS.toFinset, ∀ᶠ y in 𝓝 x,
      (W p).indicator (fun y => c p * jac n z g y) y = (if x ∈ W p then c p else 0) * jac n z g y := by
    intro p hp
    have hpS : p ∈ zeroSet n g := hS.mem_toFinset.1 hp
    obtain ⟨hWo, -, -, hfr, -⟩ := hW.2 p hpS
    by_cases hxW : x ∈ W p
    · filter_upwards [hWo.mem_nhds hxW] with y hy
      simp [hy, hxW]
    · have hxc : x ∉ closure (W p) := by
        intro hc
        have hfx : x ∈ frontier (W p) := ⟨hc, by rwa [hWo.interior_eq]⟩
        exact absurd (hfr x hfx) (not_le.2 hx)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
      have hyW : y ∉ W p := fun h => hy (subset_closure h)
      simp [hyW, hxW]
  filter_upwards [(Filter.eventually_all_finset _).2 key] with y hy
  rw [ap_gt_eq_sum n z g c W hS y, Finset.sum_mul]
  exact Finset.sum_congr rfl hy

theorem ap_cutExt_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (χ : ℝ → ℝ) (ε : ℝ)
    (hcont : Continuous (ev n g ph r)) (hχ0 : ∀ t, 1 ≤ t → χ t = 0) (hε : 0 < ε) (x : M)
    (hx : ε ^ 2 < ev n g ph r x) :
    cutExt n z g ph r c W χ ε =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hx] with y hy
  simp only [cutExt]
  rw [hχ0 _ ((one_le_div (by positivity)).2 hy.le)]
  simp

theorem ap_cutExt_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ)
    (ε : ℝ) (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) (x : M)
    (hx : ev n g ph r x < m) :
    cutExt n z g ph r c W χ ε =ᶠ[𝓝 x] fun y => (χ (ev n g ph r y / ε ^ 2) : ℂ) *
      ((∑ p ∈ hS.toFinset, if x ∈ W p then c p else 0) * jac n z g y) := by
  filter_upwards [ap_gt_local n z g ph r c W m hS hW x hx] with y hy
  simp only [cutExt, hy]

theorem ap_smooth_cutExt {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (hph : SmoothR n z ph) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) (hχs : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ t, 1 ≤ t → χ t = 0) (hε : 0 < ε) (hm : ε ^ 2 < m) :
    Smooth n z (cutExt n z g ph r c W χ ε) := by
  have hev := ap_smoothR_ev n z g hg ph hph r
  have hcont := ap_cont_of_smoothR n z hz _ hev
  apply ap_smooth_of_local
  intro x
  by_cases hx : ev n g ph r x < m
  · refine ⟨_, ?_, ap_cutExt_local n z g ph r c W m χ ε hS hW x hx⟩
    have hk : SmoothR n z (fun y => χ (ev n g ph r y / ε ^ 2)) :=
      SmoothR.comp n z (fun t => χ (t / ε ^ 2)) (hχs.comp (contDiff_id.div_const _)) _ hev
    exact Smooth.mul n z _ _ hk (Holo.smooth n z _ (Holo.mul n z _ _ (Holo.const n z _)
      (ap_holo_jac n z g hg)))
  · exact ⟨fun _ => 0, Smooth.const n z 0,
      ap_cutExt_zero n z g ph r c W χ ε hcont hχ0 hε x (by linarith [not_lt.1 hx])⟩

theorem ap_hasDerivAt_chi (χ : ℝ → ℝ) (hχs : ContDiff ℝ ∞ χ) (ε t : ℝ) :
    HasDerivAt (fun t => χ (t / ε ^ 2)) (deriv χ (t / ε ^ 2) * (1 / ε ^ 2)) t := by
  have h1 : HasDerivAt χ (deriv χ (t / ε ^ 2)) (t / ε ^ 2) :=
    ((hχs.differentiable (by simp)) _).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => t / ε ^ 2) (1 / ε ^ 2) t := (hasDerivAt_id t).div_const _
  exact h1.comp t h2

theorem ap_dbar_cutExt {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (hph : SmoothR n z ph) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) (hχs : ContDiff ℝ ∞ χ)
    (x : M) (hx : ev n g ph r x < m) (ξ : Fin n → ℂ) :
    dbarDot n z (cutExt n z g ph r c W χ ε) x ξ =
      ((deriv χ (ev n g ph r x / ε ^ 2) * (1 / ε ^ 2) : ℝ) : ℂ) * gt n z g c W x *
        dbarDot n z (fun y => (ev n g ph r y : ℂ)) x ξ := by
  have hev := ap_smoothR_ev n z g hg ph hph r
  have hloc := ap_cutExt_local n z g ph r c W m χ ε hS hW x hx
  have hgx := (ap_gt_local n z g ph r c W m hS hW x hx).self_of_nhds
  set C := ∑ p ∈ hS.toFinset, if x ∈ W p then c p else 0
  have hJ : Holo n z (fun y => C * jac n z g y) :=
    Holo.mul n z _ _ (Holo.const n z _) (ap_holo_jac n z g hg)
  have hk : SmoothR n z (fun y => χ (ev n g ph r y / ε ^ 2)) :=
    SmoothR.comp n z (fun t => χ (t / ε ^ 2)) (hχs.comp (contDiff_id.div_const _)) _ hev
  have hderiv : deriv (fun t => χ (t / ε ^ 2)) (ev n g ph r x) =
      deriv χ (ev n g ph r x / ε ^ 2) * (1 / ε ^ 2) := (ap_hasDerivAt_chi χ hχs ε _).deriv
  unfold dbarDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ap_db_congr n z hz j _ _ x hloc,
    db_mul n z _ _ (Smooth.ck n z 1 _ hk) (Smooth.ck n z 1 _ (Holo.smooth n z _ hJ)) j x,
    Holo.db_eq_zero n z _ hJ j x,
    db_comp_real n z (fun t => χ (t / ε ^ 2)) (hχs.comp (contDiff_id.div_const _)) _
      (SmoothR.ckR n z 1 _ hev) j x, hderiv, hgx]
  ring

theorem ap_measurable_gt {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
    (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) :
    Measurable (gt n z g c W) := by
  have hJ : Continuous (jac n z g) :=
    Smooth.continuous n z hz _ (Holo.smooth n z _ (ap_holo_jac n z g hg))
  have h : gt n z g c W = fun y => ∑ p ∈ hS.toFinset, (W p).indicator (fun y => c p * jac n z g y) y :=
    funext (ap_gt_eq_sum n z g c W hS)
  rw [h]
  apply Finset.measurable_sum
  intro p hp
  exact (measurable_const.mul hJ.measurable).indicator
    (hW.2 p (hS.mem_toFinset.1 hp)).1.measurableSet

theorem ap_cutExt_support {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (x : M) (hx : x ∉ ⋃ p ∈ hS.toFinset, closure (W p)) :
    cutExt n z g ph r c W χ ε x = 0 := by
  simp only [cutExt, ap_gt_eq_sum n z g c W hS x]
  rw [Finset.sum_eq_zero, mul_zero]
  intro p hp
  have : x ∉ W p := fun h => hx (Set.mem_biUnion hp (subset_closure h))
  simp [this]

end ReciprocityTheory.L2DbarEstimates.I
