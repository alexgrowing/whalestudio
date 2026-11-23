import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem holo_continuous_of_isLocalHomeomorph {M : Type*} [TopologicalSpace M] (n : ℕ)
    (z : M → V n) (hz : IsLocalHomeomorph z) (f : M → ℂ) (hf : Holo n z f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hx' : e x ∈ e.target := e.map_source hx
  have h1 : ContinuousAt (f ∘ e.symm) (e x) :=
    (hf e he).continuousOn.continuousAt (e.open_target.mem_nhds hx')
  have h3 : ContinuousAt ((f ∘ e.symm) ∘ e) x := h1.comp (e.continuousAt hx)
  refine h3.congr ?_
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  show f (e.symm (e y)) = f y
  rw [e.left_inv hy]

theorem locallyCompactSpace_of_isLocalHomeomorph {M : Type*} [TopologicalSpace M] (n : ℕ)
    (z : M → V n) (hz : IsLocalHomeomorph z) : LocallyCompactSpace M := by
  have : ∀ x : M, ∃ e : OpenPartialHomeomorph M (V n), x ∈ e.source := fun x =>
    let ⟨e, hx, _⟩ := hz x; ⟨e, hx⟩
  choose c hc using this
  have hb : ∀ x : M, (𝓝 x).HasBasis
      (fun s ↦ s ∈ 𝓝 (c x x) ∧ IsCompact s ∧ s ⊆ (c x).target)
      fun s ↦ (c x).symm '' s := fun x ↦ by
    rw [← (c x).symm_map_nhds_eq (hc x)]
    exact ((compact_basis_nhds (c x x)).hasBasis_self_subset
      ((c x).open_target.mem_nhds ((c x).map_source (hc x)))).map _
  refine .of_hasBasis hb ?_
  rintro x s ⟨_, h₂, h₃⟩
  exact h₂.image_of_continuousOn ((c x).continuousOn_symm.mono h₃)

theorem ev_pos_of_not_mem_zeroSet {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ)
    (r : ℝ) (hr : 0 < r) (x : M) (hx : x ∉ zeroSet n g) : 0 < ev n g ph r x := by
  simp only [zeroSet, Set.mem_ofPred_eq, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  have hs : 0 < ∑ i, ‖g i x‖ ^ 2 :=
    Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  exact div_pos (mul_pos hs (Real.exp_pos _)) (pow_pos hr 2)

theorem localData (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] : LocalStatement n M := by
  intro z g ph r N hz hg hph hr hS _hJ hN
  have := locallyCompactSpace_of_isLocalHomeomorph n z hz
  obtain ⟨U, hU, hUd⟩ := hS.t2_separation
  have hex : ∀ p ∈ zeroSet n g, ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ closure V ⊆ N p ∩ U p ∧
      IsCompact (closure V) := by
    intro p hp
    obtain ⟨V, hVo, hpV, hcl, hcpt⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := p)) ((hN p hp).1.inter (hU p).2)
      (Set.singleton_subset_iff.mpr ⟨(hN p hp).2, (hU p).1⟩)
    exact ⟨V, hVo, hpV (Set.mem_singleton p), hcl, hcpt⟩
  choose! W hWo hpW hWcl hWc using hex
  have hgc : ∀ i, Continuous (g i) := fun i =>
    holo_continuous_of_isLocalHomeomorph n z hz _ (hg i)
  have hphc : Continuous ph :=
    (Complex.continuous_re.comp (Smooth.continuous n z hz _ hph)).congr (fun x => by simp)
  have hevc : Continuous (ev n g ph r) := by
    unfold ev
    fun_prop
  have hfr : ∀ p ∈ zeroSet n g, ∀ x ∈ frontier (W p), x ∉ zeroSet n g := by
    intro p hp x hx hxS
    have hxU : x ∈ U p := (hWcl p hp (frontier_subset_closure hx)).2
    by_cases hxp : x = p
    · rw [hxp, (hWo p hp).frontier_eq] at hx
      exact hx.2 (hpW p hp)
    · exact Set.disjoint_left.mp (hUd hxS hp hxp) (hU x).1 hxU
  have hK : IsCompact (⋃ p ∈ zeroSet n g, frontier (W p)) :=
    hS.isCompact_biUnion fun p hp =>
      (hWc p hp).of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hpos : ∀ x ∈ ⋃ p ∈ zeroSet n g, frontier (W p), 0 < ev n g ph r x := by
    intro x hx
    obtain ⟨p, hp, hxf⟩ := Set.mem_iUnion₂.mp hx
    exact ev_pos_of_not_mem_zeroSet n g ph r hr x (hfr p hp x hxf)
  obtain ⟨m, hm, hmK⟩ := hK.exists_forall_le' hevc.continuousOn hpos
  refine ⟨W, m, ⟨hm, fun p hp => ⟨hWo p hp, hpW p hp, hWc p hp,
    fun x hx => hmK x (Set.mem_biUnion hp hx), fun q hq hqp => ?_⟩⟩,
    fun p hp x hx => (hWcl p hp (subset_closure hx)).1⟩
  exact Disjoint.mono (fun x hx => (hWcl p hp hx).2) (fun x hx => (hWcl q hq hx).2)
    (hUd hp hq hqp.symm)

end ReciprocityTheory.L2DbarEstimates.I
