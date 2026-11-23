import Mathlib

open Set Filter Topology

namespace GlobalTheory

theorem frame_term_continuousAt {X : Type} [TopologicalSpace X] (ρ : ℝ × ℝ → ℝ) (hρ : Continuous ρ)
    (a : ℝ × ℝ → ℂ) (c : X → ℂ) (p : X → ℝ × ℝ) (hp : Continuous p) (x : X)
    (h : p x ∈ tsupport ρ → ContinuousAt a (p x) ∧ ContinuousAt c x) :
    ContinuousAt (fun y => (ρ (p y) : ℂ) * a (p y) * c y) x := by
  by_cases hx : p x ∈ tsupport ρ
  · obtain ⟨ha, hc⟩ := h hx
    have h1 : ContinuousAt (fun y => (ρ (p y) : ℂ)) x :=
      (Complex.continuous_ofReal.comp (hρ.comp hp)).continuousAt
    exact (h1.mul (ha.comp hp.continuousAt)).mul hc
  · have h0 : ρ =ᶠ[𝓝 (p x)] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have h0' : (fun y => (ρ (p y) : ℂ) * a (p y) * c y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [hp.continuousAt.preimage_mem_nhds h0] with y hy
      simp only [mem_preimage, mem_setOf_eq, Pi.zero_apply] at hy
      simp [hy]
    exact continuousAt_const.congr h0'.symm

theorem frame_extend_near_fibre : ∀ (B : Type) [TopologicalSpace B] (b₀ : B) (J : Type)
    (O : J → Set (B × ℝ × ℝ)) (s : J → B × ℝ × ℝ → ℂ) (K : Set (ℝ × ℝ)), IsCompact K →
    (∀ i, IsOpen (O i)) → (∀ q, ∃ i, q ∈ O i) → (∀ i, ∀ q ∈ O i, s i q ≠ 0) →
    (∀ i, ContinuousOn (fun v : ℝ × ℝ => s i (b₀, v)) {v | (b₀, v) ∈ O i}) →
    (∀ i j, ContinuousOn (fun q => s i q / s j q) (O i ∩ O j)) →
    ∃ V ∈ nhds b₀, ∃ r : B × ℝ × ℝ → ℂ, (∀ q ∈ V ×ˢ K, r q ≠ 0) ∧
      ∀ i, ContinuousOn (fun q => s i q * r q) (O i ∩ V ×ˢ K) := by
  intro B _ b₀ J O s K hK hO hcov hne hcont hratio
  classical
  let U : J → Set (ℝ × ℝ) := fun j => {v | (b₀, v) ∈ O j}
  have hUo : ∀ j, IsOpen (U j) := fun j =>
    (hO j).preimage (continuous_const.prodMk continuous_id)
  have hKU : K ⊆ ⋃ j, U j := fun v _ => by
    obtain ⟨j, hj⟩ := hcov (b₀, v)
    exact mem_iUnion.2 ⟨j, hj⟩
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed U hUo hKU
  have hfin : {j | (tsupport (f j) ∩ K).Nonempty}.Finite :=
    f.locallyFinite.closure.finite_nonempty_inter_compact hK
  let F := hfin.toFinset
  let r : B × ℝ × ℝ → ℂ := fun q => ∑ j ∈ F, (f j q.2 : ℂ) * (s j (b₀, q.2) / s j q)
  have hV1 : ∀ᶠ b in 𝓝 b₀, ∀ j ∈ F, ∀ v ∈ tsupport (f j) ∩ K, (b, v) ∈ O j := by
    refine (Filter.eventually_all_finset F).2 fun j _ => ?_
    refine (hK.inter_left (isClosed_tsupport _)).eventually_forall_of_forall_eventually
      (P := fun b v => (b, v) ∈ O j) fun v hv => ?_
    exact (hO j).mem_nhds (hf j hv.1)
  let V₁ := {b | ∀ j ∈ F, ∀ v ∈ tsupport (f j) ∩ K, (b, v) ∈ O j}
  have hV₁ : V₁ ∈ 𝓝 b₀ := hV1
  have hb₀ : b₀ ∈ V₁ := mem_of_mem_nhds hV₁
  have hr₀ : ∀ v ∈ K, r (b₀, v) = 1 := by
    intro v hv
    have hsupp : ∀ j, f j v ≠ 0 → j ∈ F ∧ s j (b₀, v) ≠ 0 := by
      intro j hj
      have hvt : v ∈ tsupport (f j) := subset_tsupport _ hj
      exact ⟨hfin.mem_toFinset.2 ⟨v, hvt, hv⟩, hne j _ (hf j hvt)⟩
    have h1 : ∑ j ∈ F, (f j v : ℂ) * (s j (b₀, v) / s j (b₀, v)) = ∑ j ∈ F, (f j v : ℂ) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : f j v = 0
      · simp [h]
      · rw [div_self (hsupp j h).2, mul_one]
    have h2 : ∑ᶠ j, f j v = ∑ j ∈ F, f j v :=
      finsum_eq_sum_of_support_subset _ (fun j hj => Finset.mem_coe.2 (hsupp j hj).1)
    show ∑ j ∈ F, (f j v : ℂ) * (s j (b₀, v) / s j (b₀, v)) = 1
    rw [h1, ← Complex.ofReal_sum, ← h2, f.sum_eq_one hv, Complex.ofReal_one]
  have hcontr : ∀ i, ContinuousOn (fun q => s i q * r q) (O i ∩ V₁ ×ˢ K) := by
    intro i
    have heq : EqOn (fun q => ∑ j ∈ F, (f j q.2 : ℂ) * s j (b₀, q.2) * (s i q / s j q))
        (fun q => s i q * r q) (O i ∩ V₁ ×ˢ K) := by
      intro q _
      simp only [r, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    refine ContinuousOn.congr ?_ heq.symm
    intro q hq
    refine ContinuousAt.continuousWithinAt ?_
    refine tendsto_finset_sum _ fun j _ => ?_
    refine (frame_term_continuousAt (f j) (f j).continuous (fun v => s j (b₀, v))
      (fun q => s i q / s j q) Prod.snd continuous_snd q fun ht => ?_).tendsto
    have hjF : j ∈ F := hfin.mem_toFinset.2 ⟨q.2, ht, hq.2.2⟩
    have hqj : q ∈ O j := hq.2.1 j hjF q.2 ⟨ht, hq.2.2⟩
    constructor
    · have hb : (b₀, q.2) ∈ O j := hf j ht
      exact (hcont j).continuousAt ((hUo j).mem_nhds hb)
    · exact (hratio i j).continuousAt (((hO i).inter (hO j)).mem_nhds ⟨hq.1, hqj⟩)
  have hev : ∀ᶠ b in 𝓝 b₀, ∀ v ∈ K, (b ∈ V₁ ∧ v ∈ K) → r (b, v) ≠ 0 := by
    refine hK.eventually_forall_of_forall_eventually
      (P := fun b v => (b ∈ V₁ ∧ v ∈ K) → r (b, v) ≠ 0) fun v hv => ?_
    obtain ⟨i, hi⟩ := hcov (b₀, v)
    have hmem : (b₀, v) ∈ O i ∩ V₁ ×ˢ K := ⟨hi, hb₀, hv⟩
    have hg : s i (b₀, v) * r (b₀, v) ≠ 0 := by
      rw [hr₀ v hv, mul_one]; exact hne i _ hi
    have h1 := Filter.Tendsto.eventually (hcontr i _ hmem) (eventually_ne_nhds hg)
    rw [eventually_nhdsWithin_iff] at h1
    filter_upwards [h1, (hO i).mem_nhds hi] with z hz hzi hzVK
    exact right_ne_zero_of_mul (hz ⟨hzi, hzVK⟩)
  refine ⟨{b | b ∈ V₁ ∧ ∀ v ∈ K, (b ∈ V₁ ∧ v ∈ K) → r (b, v) ≠ 0}, inter_mem hV₁ hev, r, ?_,
    fun i => (hcontr i).mono ?_⟩
  · rintro ⟨b, v⟩ ⟨⟨hb1, hb2⟩, hv⟩
    exact hb2 v hv ⟨hb1, hv⟩
  · rintro ⟨b, v⟩ ⟨hi, ⟨hb1, _⟩, hv⟩
    exact ⟨hi, hb1, hv⟩

end GlobalTheory
