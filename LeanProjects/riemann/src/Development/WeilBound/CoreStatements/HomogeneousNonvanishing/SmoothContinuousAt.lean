import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.GMonomial
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

namespace PositivityTheory.UnitarySelfGeneration.CSnc

open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology Set Asymptotics HolomorphicMinorCharts

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem smooth_continuousAt {A : FinHolAtlas e X} {U : Set X} (hU : IsOpen U) {g : X → ℝ} (hg : A.SmoothOn U g)
    {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hc := ((hg j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds
    (x := A.chart j x) ⟨(A.chart j).map_source hj, by rwa [Set.mem_preimage, (A.chart j).left_inv hj]⟩)).continuousAt
  exact ((A.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := g) (x := x) (by simpa using hj)).mpr (by simpa using hc)

theorem section_zero {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} (hs : IsSection A L s) {x x' y : X}
    (h : y ∈ L.U x) (h' : y ∈ L.U x') (h0 : s x y = 0) : s x' y = 0 := by
  have := hs.2 x x' y ⟨h, h'⟩
  rw [h0, norm_zero, zero_mul, eq_comm, mul_eq_zero] at this
  exact norm_eq_zero.mp (this.resolve_right (Real.exp_pos _).ne')

def Loc (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (W : Fin n → Set X) (x : X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin n → Option (Fin e)) (mm : Fin e → ℕ) : Prop :=
  IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ψ.source ⊆ L.U x ∧ (∀ k k' i, σ k = some i → σ k' = some i → k = k') ∧
    (∀ k, W k ∩ ψ.source = {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0}) ∧
    (∀ i, mm i ≠ 0 → ψ x i = 0 ∧ ∃ k, σ k = some i) ∧
    ∃ u : X → ℂ, A.HoloOn ψ.source u ∧ (∀ y ∈ ψ.source, u y ≠ 0) ∧ ∀ y ∈ ψ.source, s x y = u y * ∏ i, ψ y i ^ mm i

theorem exists_loc {A : FinHolAtlas e X} {L₀ L : LocPot X} {s₀ s : X → X → ℂ} {n : ℕ} {m₀ : Fin n → ℕ}
    {W : Fin n → Set X} (h₀ : IsSNC A L₀ s₀ m₀ W) (hs : IsSection A L s) (hb : bdry s ⊆ {x | s₀ x x = 0})
    (hz : ∀ x x', ∀ y ∈ L₀.U x ∩ L₀.U x', (s₀ x y = 0 ↔ s₀ x' y = 0)) (x : X) :
    ∃ ψ σ mm, Loc A L s W x ψ σ mm := by
  classical
  obtain ⟨ψ, hψ, hx, hU, σ, hσ, hW, u₀, -, hu₀, hE⟩ := h₀ x
  set c := ψ x with hc
  have hO : ψ.target ∩ ψ.symm ⁻¹' L.U x ∩ {v | ∀ i, c i ≠ 0 → v i ≠ 0} ∈ 𝓝 c := by
    refine inter_mem ((ψ.isOpen_inter_preimage_symm (L.isOpen_U x)).mem_nhds
      ⟨ψ.map_source hx, by rw [Set.mem_preimage, hc, ψ.left_inv hx]; exact L.mem_U x⟩) ?_
    refine eventually_all.mpr fun i => ?_
    by_cases hi : c i = 0
    · exact Eventually.of_forall fun v h => absurd hi h
    · filter_upwards [(continuous_apply i).continuousAt.eventually_ne hi] with v hv _ using hv
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hO
  have hsh : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, z + c ∈ Metric.ball c r := fun z hz => by
    simpa using hz
  obtain ⟨mm, u, hm, hu, hu0, hF⟩ := g_monomial e (Finset.univ.filter fun i => c i = 0 ∧ ∃ k, σ k = some i)
    (fun z => s x (ψ.symm (z + c))) r hr
    (fun z hz => AnalyticAt.comp (g := s x ∘ ψ.symm) (f := fun z => z + c)
      (holo_compat hψ (hs.1 x) (hball (hsh z hz)).1.1 (hball (hsh z hz)).1.2) (analyticAt_id.add analyticAt_const))
    (by
      intro z hzb hS h0
      obtain ⟨⟨h1, h2⟩, h3⟩ := hball (hsh z hzb)
      have h4 := ψ.map_target h1
      have h5 : s₀ x (ψ.symm (z + c)) = 0 :=
        (hz x _ _ ⟨hU h4, L₀.mem_U _⟩).mpr (hb (section_zero hs h2 (L.mem_U _) h0))
      rw [hE _ h4, mul_eq_zero, Finset.prod_eq_zero_iff] at h5
      obtain ⟨k, -, hk⟩ := h5.resolve_left (hu₀ _ h4)
      rcases h : σ k with _ | i
      · simp [h] at hk
      · simp only [h, ψ.right_inv h1] at hk
        have h6 := eq_zero_of_pow_eq_zero hk
        by_cases hi : c i = 0
        · exact hS i (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hi, k, h⟩)
            (by simpa [hi] using h6)
        · exact h3 i hi h6)
  have hop : IsOpen (ψ.source ∩ ψ ⁻¹' Metric.ball c r) := ψ.isOpen_inter_preimage Metric.isOpen_ball
  have hsub : ∀ y, ψ y ∈ Metric.ball c r → ψ y - c ∈ Metric.ball (0 : Fin e → ℂ) r := fun y hy => by
    simpa [dist_eq_norm] using hy
  have hm' : ∀ i, mm i ≠ 0 → c i = 0 ∧ ∃ k, σ k = some i := fun i hi => by
    by_contra h
    exact hi (hm i (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h))
  refine ⟨ψ.restrOpen _ hop, σ, mm, fun j => ⟨(hψ j).1.mono fun v hv => ⟨hv.1, hv.2.1⟩,
    (hψ j).2.mono fun v hv => ⟨hv.1.1, hv.2⟩⟩, ⟨hx, hx, Metric.mem_ball_self hr⟩, fun y hy => ?_, hσ, fun k => ?_, hm',
    fun y => u (ψ y - c), ?_, fun y hy => hu0 _ (hsub y hy.2.2), fun y hy => ?_⟩
  · have := (hball hy.2.2).1.2
    rwa [Set.mem_preimage, ψ.left_inv hy.1] at this
  · ext y
    constructor
    · rintro ⟨h1, h2⟩
      have : y ∈ W k ∩ ψ.source := ⟨h1, h2.1⟩
      rw [hW] at this
      exact ⟨h2, this.2⟩
    · rintro ⟨h1, h2⟩
      have : y ∈ W k ∩ ψ.source := by rw [hW]; exact ⟨h1.1, h2⟩
      exact ⟨this.1, h1⟩
  · exact holoOn_of_compat hψ (G := fun v => u (v - c)) (fun y hy => hy.1) fun y hy =>
      AnalyticAt.comp (g := u) (f := fun v => v - c) (hu _ (hsub y hy.2.2)) (analyticAt_id.sub analyticAt_const)
  · have := hF _ (hsub y hy.2.2)
    simp only [sub_add_cancel, ψ.left_inv hy.1] at this
    rw [this]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : mm i = 0
    · simp [hi]
    · rw [Pi.sub_apply, (hm' i hi).1, sub_zero]
      rfl

theorem theta_mul {𝕜 : Type} [NormedField 𝕜] {l : Filter X} {v f : X → 𝕜} {c : 𝕜} (hc : c ≠ 0)
    (hv : Tendsto v l (𝓝 c)) : (fun w => v w * f w) =Θ[l] f :=
  (((isEquivalent_const_iff_tendsto hc).mpr hv).mul (IsEquivalent.refl (u := f))).isTheta.trans
    ((isTheta_const_mul_left hc).mpr isTheta_rfl)

variable {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} {n : ℕ} {W : Fin n → Set X}

theorem Loc.mem_iff {x : X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} {σ : Fin n → Option (Fin e)} {mm : Fin e → ℕ}
    (h : Loc A L s W x ψ σ mm) {y : X} (hy : y ∈ ψ.source) (k : Fin n) :
    y ∈ W k ↔ ∃ i, σ k = some i ∧ ψ y i = 0 := by
  constructor
  · intro h1
    have : y ∈ W k ∩ ψ.source := ⟨h1, hy⟩
    rw [h.2.2.2.2.1] at this
    exact this.2
  · intro h1
    have : y ∈ W k ∩ ψ.source := by rw [h.2.2.2.2.1]; exact ⟨hy, h1⟩
    exact this.1

theorem Loc.theta {x : X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} {σ : Fin n → Option (Fin e)} {mm : Fin e → ℕ}
    (h : Loc A L s W x ψ σ mm) {y : X} (hy : y ∈ ψ.source) {k : Fin n} {i : Fin e} (hk : σ k = some i)
    (hg : ∀ k', k' ≠ k → y ∉ W k') : s x =Θ[𝓝 y] fun w => ψ w i ^ mm i := by
  classical
  obtain ⟨u, hu, hu0, hE⟩ := h.2.2.2.2.2.2
  have h1 : s x =ᶠ[𝓝 y] fun w => (u w * ∏ j ∈ Finset.univ.erase i, ψ w j ^ mm j) * ψ w i ^ mm i := by
    filter_upwards [ψ.open_source.mem_nhds hy] with w hw
    rw [hE w hw, mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  refine h1.isTheta.trans (theta_mul (c := u y * ∏ j ∈ Finset.univ.erase i, ψ y j ^ mm j) ?_ ?_)
  · refine mul_ne_zero (hu0 y hy) (Finset.prod_ne_zero_iff.mpr fun j hj => ?_)
    by_cases hj0 : mm j = 0
    · simp [hj0]
    · obtain ⟨-, k', hk'⟩ := h.2.2.2.2.2.1 j hj0
      refine pow_ne_zero _ fun h0 => hg k' ?_ ((h.mem_iff hy k').mpr ⟨j, hk', h0⟩)
      rintro rfl
      rw [hk] at hk'
      exact Finset.ne_of_mem_erase hj (Option.some.inj hk').symm
  · exact (holo_continuousAt hu hy).tendsto.mul (tendsto_finsetProd _ fun j _ =>
      (((continuous_apply j).continuousAt.comp (ψ.continuousAt hy)).pow _).tendsto)

theorem le_of_isBigO (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) {y : X} (hy : y ∈ ψ.source) {i : Fin e}
    (hi : ψ y i = 0) {a b : ℕ} (h : (fun w => ψ w i ^ a) =O[𝓝 y] fun w => ψ w i ^ b) : b ≤ a := by
  by_contra hab
  push Not at hab
  have t1 : Tendsto (fun t : ℂ => Function.update (ψ y) i t) (𝓝 0) (𝓝 (ψ y)) := by
    have := (GMon.analyticAt_update_right i (ψ y) 0).continuousAt.tendsto
    rwa [show Function.update (ψ y) i 0 = ψ y by rw [← hi, Function.update_eq_self]] at this
  have h1 := h.comp_tendsto ((tendsto_symm ψ hy).comp t1)
  have h2 : ∀ c : ℕ, ((fun w => ψ w i ^ c) ∘ ψ.symm ∘ fun t : ℂ => Function.update (ψ y) i t) =ᶠ[𝓝 0]
      fun t => t ^ c := fun c => by
    filter_upwards [t1 (ψ.open_target.mem_nhds (ψ.map_source hy))] with t ht
    simp only [Function.comp_apply]
    rw [ψ.right_inv ht]
    simp only [Function.update_self]
  have h3 := (h1.congr' (h2 a) (h2 b)).trans_isLittleO (isLittleO_pow_pow hab)
  refine isLittleO_irrefl ?_ h3
  refine Frequently.filter_mono (Eventually.frequently (f := 𝓝[≠] (0 : ℂ)) ?_) nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin] with t ht using pow_ne_zero _ ht

theorem Loc.le_generic (hL : IsPotential A L) (hs : IsSection A L s) {x x' : X}
    {ψ ψ' : OpenPartialHomeomorph X (Fin e → ℂ)} {σ σ' : Fin n → Option (Fin e)} {mm mm' : Fin e → ℕ}
    (h : Loc A L s W x ψ σ mm) (h' : Loc A L s W x' ψ' σ' mm') {y : X} (hy : y ∈ ψ.source) (hy' : y ∈ ψ'.source)
    {k : Fin n} {i i' : Fin e} (hk : σ k = some i) (hk' : σ' k = some i') (hyW : y ∈ W k)
    (hg : ∀ k', k' ≠ k → y ∉ W k') : mm' i' ≤ mm i := by
  have hi : ψ y i = 0 := by
    obtain ⟨j, hj, h0⟩ := (h.mem_iff hy k).mp hyW
    rw [hk] at hj
    rwa [Option.some.inj hj]
  refine le_of_isBigO ψ hy hi ?_
  have h1 : s x =Θ[𝓝 y] s x' := by
    have e1 : (fun w => ‖s x w‖) =ᶠ[𝓝 y] fun w => Real.exp (L.φ x w - L.φ x' w) * ‖s x' w‖ := by
      filter_upwards [ψ.open_source.mem_nhds hy, ψ'.open_source.mem_nhds hy'] with w h1 h2
      have := hs.2 x x' w ⟨h.2.2.1 h1, h'.2.2.1 h2⟩
      rw [Real.exp_neg, Real.exp_neg] at this
      rw [Real.exp_sub]
      have p1 := (Real.exp_pos (L.φ x w)).ne'
      have p2 := (Real.exp_pos (L.φ x' w)).ne'
      field_simp at this ⊢
      linarith
    have e2 := e1.isTheta.trans (theta_mul (Real.exp_pos _).ne'
      ((smooth_continuousAt (L.isOpen_U x) (hL.1 x) (h.2.2.1 hy)).sub
        (smooth_continuousAt (L.isOpen_U x') (hL.1 x') (h'.2.2.1 hy'))).rexp.tendsto)
    exact isTheta_norm_left.mp (isTheta_norm_right.mp e2)
  have h2 : (fun w => ψ' w i') =O[𝓝 y] fun w => ψ w i := by
    have ha : AnalyticAt ℂ ((fun w => ψ' w i') ∘ ψ.symm) (ψ y) :=
      holo_compat h.1 (holoOn_of_compat h'.1 (G := fun v => v i') subset_rfl fun _ _ =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i').analyticAt _) (ψ.map_source hy)
        (by rwa [ψ.left_inv hy])
    obtain ⟨C, hC⟩ := GMon.isBigO_coord i ha hi (by
      filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hy),
        tendsto_symm ψ hy (ψ'.open_source.mem_nhds hy')] with v h1 h2 h3
      obtain ⟨j, hj, h0⟩ := (h'.mem_iff h2 k).mp ((h.mem_iff (ψ.map_target h1) k).mpr
        ⟨i, hk, by rwa [ψ.right_inv h1]⟩)
      rw [hk'] at hj
      rwa [← Option.some.inj hj] at h0)
    refine IsBigO.of_bound C ?_
    filter_upwards [(ψ.continuousAt hy).eventually hC, ψ.open_source.mem_nhds hy] with w h1 h2
    simpa only [Function.comp_apply, ψ.left_inv h2] using h1
  exact (((h.theta hy hk hg).symm.trans h1).trans (h'.theta hy' hk' hg)).isBigO.trans (h2.pow _)

theorem Loc.order_eq (hL : IsPotential A L) (hs : IsSection A L s) {x x' : X}
    {ψ ψ' : OpenPartialHomeomorph X (Fin e → ℂ)} {σ σ' : Fin n → Option (Fin e)} {mm mm' : Fin e → ℕ}
    (h : Loc A L s W x ψ σ mm) (h' : Loc A L s W x' ψ' σ' mm') {y : X} (hy : y ∈ ψ.source) (hy' : y ∈ ψ'.source)
    {k : Fin n} {i i' : Fin e} (hk : σ k = some i) (hk' : σ' k = some i') (hyW : y ∈ W k) : mm i = mm' i' := by
  classical
  have hi : ψ y i = 0 := by
    obtain ⟨j, hj, h0⟩ := (h.mem_iff hy k).mp hyW
    rw [hk] at hj
    rwa [Option.some.inj hj]
  let v : ℂ → Fin e → ℂ := fun t => Function.update (fun j => ψ y j + t) i 0
  have t1 : Tendsto v (𝓝[≠] 0) (𝓝 (ψ y)) := by
    have hc : Continuous v := Continuous.update (by fun_prop) i continuous_const
    have h0 : v 0 = ψ y := by
      simp only [v, add_zero]
      rw [← hi, Function.update_eq_self]
    exact (h0 ▸ hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have t2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ j, ψ y j + t ≠ 0 := eventually_all.mpr fun j => by
    by_cases hj : ψ y j = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hj, zero_add]
      exact ht
    · exact nhdsWithin_le_nhds (ContinuousAt.eventually_ne (g := fun t : ℂ => ψ y j + t) (by fun_prop)
        (by simpa using hj))
  obtain ⟨t, h1, h2, h3⟩ := (t2.and ((t1.eventually (ψ.open_target.mem_nhds (ψ.map_source hy))).and
    (((tendsto_symm ψ hy).comp t1).eventually (ψ'.open_source.mem_nhds hy')))).exists
  have h4 := ψ.map_target h2
  have h5 : ψ.symm (v t) ∈ W k := (h.mem_iff h4 k).mpr ⟨i, hk, by rw [ψ.right_inv h2]; simp [v]⟩
  have h6 : ∀ k', k' ≠ k → ψ.symm (v t) ∉ W k' := by
    intro k' hne hm
    obtain ⟨j, hj, h0⟩ := (h.mem_iff h4 k').mp hm
    rw [ψ.right_inv h2] at h0
    by_cases hji : j = i
    · exact hne (h.2.2.2.1 k' k i (hji ▸ hj) hk)
    · simp only [v, Function.update_of_ne hji] at h0
      exact h1 j h0
  exact le_antisymm (h'.le_generic hL hs h h3 h4 hk' hk h5 h6) (h.le_generic hL hs h' h4 h3 hk hk' h5 h6)

theorem prod_opt {σ : Fin n → Option (Fin e)} (hσ : ∀ k k' i, σ k = some i → σ k' = some i → k = k')
    (f : Fin e → ℂ) (hf : ∀ i, f i ≠ 1 → ∃ k, σ k = some i) : ∏ k, (σ k).elim 1 f = ∏ i, f i := by
  classical
  have h1 : ∀ k, (σ k).elim 1 f = ∏ i, if σ k = some i then f i else 1 := fun k => by
    rcases σ k with _ | j
    · simp
    · simp
  simp only [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : f i = 1
  · simp [hi]
  · obtain ⟨k, hk⟩ := hf i hi
    rw [Finset.prod_eq_single k, if_pos hk]
    · intro k' _ hne
      exact if_neg fun h => hne (hσ k' k i h hk)
    · simp

theorem snc_of_loc [CompactSpace X] (hL : IsPotential A L) (hs : IsSection A L s)
    (hloc : ∀ x, ∃ ψ σ mm, Loc A L s W x ψ σ mm) :
    ∃ (n' : ℕ) (m : Fin n' → ℕ) (W' : Fin n' → Set X), IsSNC A L s m W' := by
  classical
  choose ψ σ mm h using hloc
  let ord : Fin n → X → ℕ := fun k y => (σ y k).elim 0 (mm y)
  have hord : ∀ x y k i, y ∈ (ψ x).source → y ∈ W k → σ x k = some i → ord k y = mm x i := by
    intro x y k i hy hW hk
    obtain ⟨j, hj, -⟩ := ((h y).mem_iff (h y).2.1 k).mp hW
    simp only [ord, hj, Option.elim_some]
    exact (h y).order_eq hL hs (h x) (h y).2.1 hy hj hk hW
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ y i, mm y i < N := by
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x => (ψ x).source) (fun x => (ψ x).open_source)
      fun x _ => mem_iUnion.mpr ⟨x, (h x).2.1⟩
    refine ⟨∑ x ∈ T, ∑ i, mm x i + 1, fun y i => Nat.lt_succ_of_le ?_⟩
    by_cases h0 : mm y i = 0
    · rw [h0]; exact Nat.zero_le _
    obtain ⟨h1, k, hk⟩ := (h y).2.2.2.2.2.1 i h0
    have hW : y ∈ W k := ((h y).mem_iff (h y).2.1 k).mpr ⟨i, hk, h1⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hT (mem_univ y))
    obtain ⟨j, hj, -⟩ := ((h x).mem_iff hyx k).mp hW
    rw [← hord y y k i (h y).2.1 hW hk, hord x y k j hyx hW hj]
    exact (Finset.single_le_sum (f := mm x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun x => ∑ i, mm x i) (fun _ _ => Nat.zero_le _) hx)
  let E : Fin (n * N) ≃ Fin n × Fin N := finProdFinEquiv.symm
  refine ⟨n * N, fun q => (E q).2, fun q => {y | y ∈ W (E q).1 ∧ ord (E q).1 y = (E q).2}, fun x => ?_⟩
  let τ : Fin (n * N) → Option (Fin e) := fun q => (σ x (E q).1).filter fun i => mm x i = (E q).2
  have hτ : ∀ q i, τ q = some i ↔ σ x (E q).1 = some i ∧ mm x i = (E q).2 := fun q i => by
    simp [τ, Option.filter_eq_some_iff]
  have hinj : ∀ q q' i, τ q = some i → τ q' = some i → q = q' := by
    intro q q' i h1 h2
    rw [hτ] at h1 h2
    exact E.injective (Prod.ext ((h x).2.2.2.1 _ _ i h1.1 h2.1) (Fin.ext (h1.2.symm.trans h2.2)))
  obtain ⟨u, hu, hu0, hE⟩ := (h x).2.2.2.2.2.2
  refine ⟨ψ x, (h x).1, (h x).2.1, (h x).2.2.1, τ, hinj, fun q => ?_, u, hu, hu0, fun y hy => ?_⟩
  · ext y
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨i, hi, h0⟩ := ((h x).mem_iff h3 _).mp h1
      exact ⟨h3, i, (hτ q i).mpr ⟨hi, (hord x y _ i h3 h1 hi).symm.trans h2⟩, h0⟩
    · rintro ⟨h3, i, hi, h0⟩
      rw [hτ] at hi
      have h1 := ((h x).mem_iff h3 _).mpr ⟨i, hi.1, h0⟩
      exact ⟨⟨h1, (hord x y _ i h3 h1 hi.1).trans hi.2⟩, h3⟩
  · rw [hE y hy, ← prod_opt hinj (fun i => ψ x y i ^ mm x i) fun i hi => ?_]
    · congr 1
      refine Finset.prod_congr rfl fun q _ => ?_
      rcases hq : τ q with _ | i
      · rfl
      · simp only [Option.elim_some]
        rw [((hτ q i).mp hq).2]
    · obtain ⟨-, k, hk⟩ := (h x).2.2.2.2.2.1 i fun h0 => hi (by rw [h0, pow_zero])
      exact ⟨E.symm (k, ⟨mm x i, hN x i⟩), (hτ _ i).mpr (by rw [E.apply_symm_apply]; exact ⟨hk, rfl⟩)⟩

end PositivityTheory.UnitarySelfGeneration.CSnc
