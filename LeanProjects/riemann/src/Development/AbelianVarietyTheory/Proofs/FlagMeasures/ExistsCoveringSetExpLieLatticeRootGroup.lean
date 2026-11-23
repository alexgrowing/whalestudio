import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical
open MeasureTheory Set

namespace GlobalTheory.LoopV.Cover

section Analysis
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

theorem near_of_finset (Λ : Submodule ℤ E) (s : Finset E) (hs : ∀ x ∈ s, x ∈ Λ) (w : E)
    (hw : w ∈ Submodule.span ℝ (s : Set E)) : ∃ l ∈ Λ, ‖w - l‖ ≤ ∑ x ∈ s, ‖x‖ := by
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 hw
  refine ⟨∑ x ∈ s, ⌊f x⌋ • x, Submodule.sum_mem _ fun x hx => Λ.smul_mem _ (hs x hx), ?_⟩
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, norm_smul]
  have h1 := Int.floor_le (f x)
  have h2 := Int.lt_floor_add_one (f x)
  have : ‖f x - (⌊f x⌋ : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  nlinarith [norm_nonneg x]

theorem finite_norm_le (Λ : Submodule ℤ E) [DiscreteTopology Λ] (r : ℝ) :
    {x : E | x ∈ Λ ∧ ‖x‖ ≤ r}.Finite := by
  have hd : DiscreteTopology Λ.toAddSubgroup := ‹_›
  have hc : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  have := Metric.finite_isBounded_inter_isClosed (s := (Λ.toAddSubgroup : Set E))
    (K := Metric.closedBall (0 : E) r) (isDiscrete_iff_discreteTopology.2 hd) Metric.isBounded_closedBall hc
  refine this.subset fun x hx => ⟨by simpa using hx.2, hx.1⟩

theorem separated (Λ : Submodule ℤ E) [DiscreteTopology Λ] (W : Submodule ℝ E)
    (hW : W ≤ Submodule.span ℝ {x | x ∈ Λ ∧ x ∈ W}) :
    ∃ ε > 0, ∀ x ∈ Λ, ∀ w ∈ W, ‖x + w‖ < ε → x ∈ W := by
  obtain ⟨s, hs, -, hsp, -⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℝ {x | x ∈ Λ ∧ x ∈ W}
  set C := ∑ x ∈ s, ‖x‖ with hC
  have hfin : ({x : E | x ∈ Λ ∧ ‖x‖ ≤ C + 1} \ (W : Set E)).Finite :=
    (finite_norm_le Λ (C + 1)).sdiff
  have hcl : IsClosed (W : Set E) := W.closed_of_finiteDimensional
  obtain ⟨δ, hδ, hd⟩ : ∃ δ > 0, ∀ x ∈ ({x : E | x ∈ Λ ∧ ‖x‖ ≤ C + 1} \ (W : Set E)),
      δ ≤ Metric.infDist x W := by
    by_cases hne : ({x : E | x ∈ Λ ∧ ‖x‖ ≤ C + 1} \ (W : Set E)).Nonempty
    · obtain ⟨x₀, hx₀, hm⟩ := Set.exists_min_image _ (fun x => Metric.infDist x (W : Set E)) hfin hne
      exact ⟨_, (hcl.notMem_iff_infDist_pos ⟨0, W.zero_mem⟩).1 hx₀.2, hm⟩
    · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  refine ⟨min 1 δ, lt_min one_pos hδ, fun x hx w hw h => ?_⟩
  obtain ⟨l, hl, hwl⟩ := near_of_finset (Λ ⊓ W.restrictScalars ℤ) s (fun x hx => hs hx) w
    (by rw [hsp]; exact hW hw)
  by_contra hxW
  have h1 : x + l ∈ ({x : E | x ∈ Λ ∧ ‖x‖ ≤ C + 1} \ (W : Set E)) := by
    refine ⟨⟨Λ.add_mem hx hl.1, ?_⟩, fun h' => hxW ?_⟩
    · have : x + l = (x + w) - (w - l) := by abel
      rw [this]
      have := norm_sub_le (x + w) (w - l)
      have := min_le_left 1 δ
      linarith
    · simpa using W.sub_mem h' hl.2
  have h2 := hd _ h1
  have h3 : Metric.infDist (x + l) (W : Set E) ≤ dist (x + l) (l - w) :=
    Metric.infDist_le_dist_of_mem (W.sub_mem hl.2 hw)
  have : dist (x + l) (l - w) = ‖x + w‖ := by rw [dist_eq_norm]; congr 1; abel
  have := min_le_right 1 δ
  linarith

theorem exists_transversal [MeasurableSpace E] [BorelSpace E] (D : Submodule ℤ E)
    (W : Submodule ℝ E) (ε : ℝ) (hε : 0 < ε) (h : ∀ x ∈ D, ∀ w ∈ W, ‖x + w‖ < ε → x ∈ W) :
    ∃ F : Set E, MeasurableSet F ∧ (∀ c ∈ F, ∀ w ∈ W, c + w ∈ F) ∧
      (∀ c, ∃ x ∈ D, c + x ∈ F) ∧ ∀ c ∈ F, ∀ x ∈ D, c + x ∈ F → x ∈ W := by
  obtain ⟨p, hp⟩ := TopologicalSpace.exists_dense_seq E
  let B : ℕ → Set E := fun n => {c | ∃ w ∈ W, ‖c + w - p n‖ < ε / 2}
  let G : ℕ → Set E := fun n => {c | ∃ x ∈ D, c + x ∈ B n}
  have hB : ∀ n, IsOpen (B n) := fun n => by
    have : B n = ⋃ w ∈ W, {c | ‖c + w - p n‖ < ε / 2} := by ext c; simp [B]
    rw [this]
    exact isOpen_biUnion fun w _ => isOpen_lt (by fun_prop) continuous_const
  have hG : ∀ n, IsOpen (G n) := fun n => by
    have : G n = ⋃ x ∈ D, (fun c => c + x) ⁻¹' B n := by ext c; simp [G]
    rw [this]
    exact isOpen_biUnion fun w _ => (hB n).preimage (by fun_prop)
  have hBW : ∀ n c w, w ∈ W → c ∈ B n → c + w ∈ B n := by
    rintro n c w hw ⟨w', hw', h'⟩
    exact ⟨w' - w, W.sub_mem hw' hw, by convert h' using 2; abel⟩
  have hGW : ∀ n c w, w ∈ W → c + w ∈ G n → c ∈ G n := by
    rintro n c w hw ⟨x, hx, h'⟩
    refine ⟨x, hx, ?_⟩
    have := hBW n _ (-w) (W.neg_mem hw) h'
    convert this using 1; abel
  have hGD : ∀ n c x, x ∈ D → c + x ∈ G n → c ∈ G n := by
    rintro n c x hx ⟨y, hy, h'⟩
    exact ⟨x + y, D.add_mem hx hy, by rwa [← add_assoc]⟩
  refine ⟨⋃ n, B n \ ⋃ m < n, G m, ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hB n).measurableSet.diff
      (isOpen_biUnion fun m _ => hG m).measurableSet
  · intro c hc w hw
    simp only [mem_iUnion, mem_sdiff, not_exists] at hc ⊢
    obtain ⟨n, h1, h2⟩ := hc
    exact ⟨n, hBW n c w hw h1, fun m hm h' => h2 m hm (hGW m c w hw h')⟩
  · intro c
    have hex : ∃ n, c ∈ G n := by
      obtain ⟨n, hn⟩ := hp.exists_dist_lt c (half_pos hε)
      exact ⟨n, 0, D.zero_mem, 0, W.zero_mem, by simpa [dist_eq_norm] using hn⟩
    obtain ⟨x, hx, hb⟩ := Nat.find_spec hex
    refine ⟨x, hx, ?_⟩
    simp only [mem_iUnion, mem_sdiff, not_exists]
    exact ⟨_, hb, fun m hm h' => Nat.find_min hex hm (hGD m c x hx h')⟩
  · intro c hc x hx hcx
    simp only [mem_iUnion, mem_sdiff, not_exists] at hc hcx
    obtain ⟨n, h1, h2⟩ := hc
    obtain ⟨m, h3, h4⟩ := hcx
    have hnm : n = m := by
      rcases lt_trichotomy n m with hl | hl | hl
      · exact absurd ⟨-x, D.neg_mem hx, by simpa using h1⟩ (h4 n hl)
      · exact hl
      · exact absurd ⟨x, hx, h3⟩ (h2 m hl)
    subst hnm
    obtain ⟨w, hw, e1⟩ := h1
    obtain ⟨w', hw', e2⟩ := h3
    refine h x hx (w' - w) (W.sub_mem hw' hw) ?_
    have : x + (w' - w) = (c + x + w' - p n) - (c + w - p n) := by abel
    rw [this]
    have := norm_sub_le (c + x + w' - p n) (c + w - p n)
    linarith

end Analysis

section Measure
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] in
theorem countable_of_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ] : Countable Λ := by
  have : (Λ : Set E).Countable := by
    refine (Set.countable_iUnion fun n : ℕ => (finite_norm_le Λ n).countable).mono fun x hx => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨n, hx, hn⟩
  exact this.to_subtype

theorem span_eq_top (Λ : Submodule ℤ E) [DiscreteTopology Λ] (Ω₀ : Set E)
    (h : IsAddFundamentalDomain Λ Ω₀ μ) (hf : μ Ω₀ ≠ ⊤) :
    Submodule.span ℝ (Λ : Set E) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨e, he⟩ : ∃ e, f e = 1 := by
    obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra hc; push Not at hc; exact hf0 (LinearMap.ext hc)
    exact ⟨(f v)⁻¹ • v, by simp [hv]⟩
  have hfc : Continuous f := f.continuous_of_finiteDimensional
  obtain ⟨δ, hδ, hsep⟩ := separated Λ ⊥ bot_le
  let P : E →ₗ[ℝ] E := LinearMap.id - f.smulRight e
  have hP : ∀ c, P c = c - f c • e := fun c => rfl
  have hPc : Continuous P := P.continuous_of_finiteDimensional
  let s : Set E := P ⁻¹' Metric.ball 0 δ
  have hso : IsOpen s := Metric.isOpen_ball.preimage hPc
  have hs : μ s = ⊤ := by
    by_contra hs
    let t : ℕ → Set E := fun n => s ∩ {c | (n : ℝ) < f c}
    have hto : ∀ n, IsOpen (t n) := fun n => hso.inter (isOpen_lt continuous_const hfc)
    have hanti : Antitone t := fun n m hnm c hc =>
      ⟨hc.1, lt_of_le_of_lt (Nat.cast_le.2 hnm : (n : ℝ) ≤ m) hc.2⟩
    have hT := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hto n).measurableSet.nullMeasurableSet)
      hanti ⟨0, ne_top_of_le_ne_top hs (measure_mono inter_subset_left)⟩
    have hemp : (⋂ n, t n) = ∅ := by
      refine eq_empty_of_forall_notMem fun c hc => ?_
      obtain ⟨n, hn⟩ := exists_nat_ge (f c)
      exact absurd (mem_iInter.1 hc n).2 (not_lt.2 hn)
    have hconst : ∀ n, μ (t n) = μ (t 0) := fun n => by
      have : t 0 = (fun c => c + (n : ℝ) • e) ⁻¹' t n := by
        ext c
        have : P (c + (n : ℝ) • e) = P c := by simp [hP, he, add_smul]
        simp [t, s, this, he]
      rw [this, measure_preimage_add_right]
    rw [hemp, measure_empty, show (⇑μ ∘ t) = fun _ => μ (t 0) from funext hconst] at hT
    have h0 : μ (t 0) = 0 := tendsto_nhds_unique tendsto_const_nhds hT
    refine ((hto 0).measure_pos μ ⟨e, ?_, ?_⟩).ne' h0
    · simp [s, hP, he, hδ]
    · simp [he]
  have := countable_of_discrete Λ
  have : Countable Λ.toAddSubgroup := this
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := Λ.toAddSubgroup) (μ := μ) (F := Ω₀) (s := s) h
    (fun x hx => by simpa [s] using hx) ((convex_ball 0 δ).linear_preimage P)
    (by rw [hs]; exact ENNReal.mul_lt_top hf.lt_top (by simp [lt_top_iff_ne_top]))
  have hfx : f x = 0 := hker (Submodule.subset_span x.2)
  have : (x : E) ∈ (⊥ : Submodule ℝ E) := hsep x x.2 0 (by simp) (by simpa [s, hP, hfx] using hx)
  exact hx0 (Subtype.ext (by simpa using this))

theorem exists_cover (Λ : Submodule ℤ E) [DiscreteTopology Λ] (Ω₀ : Set E)
    (h : IsAddFundamentalDomain Λ Ω₀ μ) (W : ℕ → Submodule ℝ E) (n : ℕ) (h0 : W 0 = ⊤)
    (hn : W n = ⊥) (hanti : Antitone W)
    (hrat : ∀ k, W k ≤ Submodule.span ℝ {x | x ∈ Λ ∧ x ∈ W k}) (φ : E → E → E)
    (hφ : ∀ k, ∀ x ∈ Λ, x ∈ W k → ∀ c, φ x c - c - x ∈ W (k + 1))
    (hcomp : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ z ∈ Λ, ∀ c, φ x (φ y c) = φ z c) :
    ∃ Ω : Set E, MeasurableSet Ω ∧ μ Ω = μ Ω₀ ∧ ∀ c, ∃ x ∈ Λ, φ x c ∈ Ω := by
  have hF : ∀ k, ∃ F : Set E, MeasurableSet F ∧ (∀ c ∈ F, ∀ w ∈ W (k + 1), c + w ∈ F) ∧
      (∀ c, ∃ x ∈ Λ ⊓ (W k).restrictScalars ℤ, c + x ∈ F) ∧
      ∀ c ∈ F, ∀ x ∈ Λ ⊓ (W k).restrictScalars ℤ, c + x ∈ F → x ∈ W (k + 1) := fun k => by
    obtain ⟨ε, hε, hs⟩ := separated Λ (W (k + 1)) (hrat _)
    exact exists_transversal _ _ ε hε fun x hx => hs x hx.1
  choose F hFm hFW hFc hFu using hF
  have key : ∀ ψ : E → E → E, (∀ k, ∀ x ∈ Λ, x ∈ W k → ∀ c, ψ x c - c - x ∈ W (k + 1)) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ z ∈ Λ, ∀ c, ψ x (ψ y c) = ψ z c) →
      ∀ c, ∃ x ∈ Λ, ψ x c ∈ ⋂ k < n, F k := by
    intro ψ h1 h2 c
    have : ∀ m, ∃ x ∈ Λ, ∀ k < m, ψ x c ∈ F k := by
      intro m
      induction m with
      | zero => exact ⟨0, Λ.zero_mem, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      | succ m ih =>
        obtain ⟨y, hy, hyF⟩ := ih
        obtain ⟨x, hx, hxF⟩ := hFc m (ψ y c)
        obtain ⟨z, hz, hzz⟩ := h2 x hx.1 y hy
        refine ⟨z, hz, fun k hk => ?_⟩
        rw [← hzz]
        have hw := h1 m x hx.1 hx.2 (ψ y c)
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · have := hFW k _ (hyF k hk) _
            ((W (k + 1)).add_mem (hanti (by omega : k + 1 ≤ m + 1) hw) (hanti (by omega : k + 1 ≤ m) hx.2))
          convert this using 1; abel
        · have := hFW k _ hxF _ hw
          convert this using 1; abel
    obtain ⟨x, hx, hh⟩ := this n
    exact ⟨x, hx, by simpa using hh⟩
  have hm : MeasurableSet (⋂ k < n, F k) :=
    MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => hFm k
  refine ⟨⋂ k < n, F k, hm, ?_, key φ hφ hcomp⟩
  have := countable_of_discrete Λ
  have : Countable Λ.toAddSubgroup := this
  have h' : IsAddFundamentalDomain Λ.toAddSubgroup Ω₀ μ := h
  refine IsAddFundamentalDomain.measure_eq (G := Λ.toAddSubgroup)
    (IsAddFundamentalDomain.mk' hm.nullMeasurableSet fun c => ?_) h'
  obtain ⟨x, hx, hxc⟩ := key (fun x c => x + c) (fun k x _ _ c => by simp)
    (fun x hx y hy => ⟨x + y, Λ.add_mem hx hy, fun c => by rw [add_assoc]⟩) c
  refine ⟨⟨x, hx⟩, hxc, fun y hy => Subtype.ext ?_⟩
  have hy' : (y : E) + c ∈ ⋂ k < n, F k := hy
  simp only [mem_iInter] at hy' hxc
  have : ∀ k ≤ n, (y : E) - x ∈ W k := by
    intro k hk
    induction k with
    | zero => simp [h0]
    | succ k ih =>
      refine hFu k _ (hxc k hk) _ ⟨Λ.sub_mem y.2 hx, ih (by omega)⟩ ?_
      convert hy' k hk using 1; abel
  have := this n le_rfl
  rw [hn] at this
  exact sub_eq_zero.1 this

end Measure

section Algebra
variable {A : Type} [Ring A] [Algebra ℝ A] (M : ℕ → Submodule ℝ A) (hanti : Antitone M)
  (hmul : ∀ i j x y, x ∈ M i → y ∈ M j → x * y ∈ M (i + j + 1))
include hanti hmul

theorem pow_sub_pow_mem {j : ℕ} {x y : A} (hx : x ∈ M 0) (hy : y ∈ M 0) (h : x - y ∈ M j)
    (i : ℕ) : x ^ (i + 2) - y ^ (i + 2) ∈ M (j + 1) := by
  have hp : ∀ i, y ^ (i + 1) ∈ M 0 := fun i => by
    induction i with
    | zero => simpa using hy
    | succ i ih => rw [pow_succ]; exact hanti (by omega) (hmul _ _ _ _ ih hy)
  have step : ∀ i, x ^ (i + 1) - y ^ (i + 1) ∈ M j → x ^ (i + 2) - y ^ (i + 2) ∈ M (j + 1) := by
    intro i hi
    have : x ^ (i + 2) - y ^ (i + 2) = x * (x ^ (i + 1) - y ^ (i + 1)) + (x - y) * y ^ (i + 1) := by
      rw [pow_succ' x (i + 1), pow_succ' y (i + 1)]; noncomm_ring
    rw [this]
    exact (M _).add_mem (by simpa using hmul _ _ _ _ hx hi) (by simpa using hmul _ _ _ _ h (hp i))
  induction i with
  | zero => exact step 0 (by simpa using h)
  | succ i ih => exact step _ (hanti (by omega) ih)

theorem trunc_sub_mem {j : ℕ} {x y : A} (hx : x ∈ M 0) (hy : y ∈ M 0) (h : x - y ∈ M j)
    (n : ℕ) : (∑ i ∈ Finset.range (n + 2), ((i.factorial : ℝ))⁻¹ • x ^ i) -
      (∑ i ∈ Finset.range (n + 2), ((i.factorial : ℝ))⁻¹ • y ^ i) - (x - y) ∈ M (j + 1) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [zero_add, Nat.factorial_one, Nat.cast_one, inv_one, pow_one, one_smul, pow_zero,
    sub_self, add_zero, add_sub_cancel_right]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← smul_sub]
  exact (M _).smul_mem _ (pow_sub_pow_mem M hanti hmul hx hy h i)

theorem rational (n : ℕ) (hn : M n = ⊥)
    (hgen : ∀ k, M (k + 1) ≤ Submodule.span ℝ {z | ∃ x ∈ M 0, ∃ y ∈ M k, z = x * y - y * x})
    (e : A → A) (he0 : e 0 = 1)
    (he : ∀ j x y, x ∈ M 0 → y ∈ M 0 → x - y ∈ M j → e x - e y - (x - y) ∈ M (j + 1))
    (Λ : Submodule ℤ A) (hΛ : ∀ x ∈ Λ, x ∈ M 0) (hsp : M 0 ≤ Submodule.span ℝ (Λ : Set A))
    (hgr : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ z ∈ Λ, e x * e y = e z) (k : ℕ) :
    M k ≤ Submodule.span ℝ {x | x ∈ Λ ∧ x ∈ M k} := by
  set S : ℕ → Submodule ℝ A := fun k => Submodule.span ℝ {x | x ∈ Λ ∧ x ∈ M k} with hS
  have he1 : ∀ j x, x ∈ M j → e x - 1 - x ∈ M (j + 1) := fun j x hx => by
    simpa [he0] using he j x 0 (hanti (Nat.zero_le _) hx) (M 0).zero_mem (by simpa using hx)
  have hinj : ∀ j x y, x ∈ M 0 → y ∈ M 0 → e x - e y ∈ M j → x - y ∈ M j := by
    intro j x y hx hy
    induction j with
    | zero => exact fun _ => (M 0).sub_mem hx hy
    | succ j ih =>
      intro h
      have := (M _).sub_mem h (he j x y hx hy (ih (hanti (by omega) h)))
      simpa using this
  have hbr : ∀ k x y, x ∈ Λ → y ∈ Λ → y ∈ M k → x * y - y * x ∈ S (k + 1) ⊔ M (k + 2) := by
    intro k x y hx hy hyk
    obtain ⟨z₁, hz₁, e₁⟩ := hgr x hx y hy
    obtain ⟨z₂, hz₂, e₂⟩ := hgr y hy x hx
    have hx0 := hΛ x hx
    have hX := he1 0 x hx0
    have hY := he1 k y hyk
    set X := e x - 1 - x
    set Y := e y - 1 - y
    have hd : e z₁ - e z₂ - (x * y - y * x) ∈ M (k + 2) := by
      have : e z₁ - e z₂ - (x * y - y * x) =
          (X * y - y * X) + (x * Y - Y * x) + (X * Y - Y * X) := by
        rw [← e₁, ← e₂]; simp only [X, Y]; noncomm_ring
      rw [this]
      refine (M _).add_mem ((M _).add_mem ((M _).sub_mem ?_ ?_) ((M _).sub_mem ?_ ?_))
        ((M _).sub_mem ?_ ?_)
      · exact hanti (by omega) (hmul _ _ _ _ hX hyk)
      · exact hanti (by omega) (hmul _ _ _ _ hyk hX)
      · exact hanti (by omega) (hmul _ _ _ _ hx0 hY)
      · exact hanti (by omega) (hmul _ _ _ _ hY hx0)
      · exact hanti (by omega) (hmul _ _ _ _ hX hY)
      · exact hanti (by omega) (hmul _ _ _ _ hY hX)
    have hc : x * y - y * x ∈ M (k + 1) :=
      (M _).sub_mem (hanti (by omega) (hmul _ _ _ _ hx0 hyk)) (hanti (by omega) (hmul _ _ _ _ hyk hx0))
    have hz : z₁ - z₂ ∈ M (k + 1) := hinj _ _ _ (hΛ _ hz₁) (hΛ _ hz₂)
      (by simpa using (M _).add_mem (hanti (by omega : k + 1 ≤ k + 2) hd) hc)
    have h2 := he _ _ _ (hΛ _ hz₁) (hΛ _ hz₂) hz
    have : x * y - y * x = (z₁ - z₂) +
        ((e z₁ - e z₂ - (z₁ - z₂)) - (e z₁ - e z₂ - (x * y - y * x))) := by abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨Λ.sub_mem hz₁ hz₂, hz⟩) ((M _).sub_mem h2 hd)
  have c1 : ∀ k, M k ≤ S k ⊔ M (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine hsp.trans (le_sup_of_le_left (Submodule.span_mono fun x hx => ⟨hx, hΛ x hx⟩))
    | succ k ih =>
      refine (hgen k).trans (Submodule.span_le.2 ?_)
      rintro _ ⟨x, hx, y, hy, rfl⟩
      obtain ⟨s, hs, m, hm, rfl⟩ := Submodule.mem_sup.1 (ih hy)
      have : x * (s + m) - (s + m) * x = (x * s - s * x) + (x * m - m * x) := by noncomm_ring
      rw [this]
      refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right ((M _).sub_mem
        (hanti (by omega) (hmul _ _ _ _ hx hm)) (hanti (by omega) (hmul _ _ _ _ hm hx))))
      have hx' := hsp hx
      clear hx hy this
      induction hx' using Submodule.span_induction with
      | zero => simp
      | add a b _ _ ha hb =>
        convert Submodule.add_mem _ ha hb using 1; noncomm_ring
      | smul r a _ ha =>
        convert Submodule.smul_mem _ r ha using 1; simp [smul_sub]
      | mem a ha =>
        induction hs using Submodule.span_induction with
        | zero => simp
        | add b c _ _ hb hc =>
          convert Submodule.add_mem _ hb hc using 1; noncomm_ring
        | smul r b _ hb =>
          convert Submodule.smul_mem _ r hb using 1; simp [smul_sub]
        | mem b hb => exact hbr k a b ha hb.1 hb.2
  have c2 : ∀ j k, n ≤ k + j → M k ≤ S k := by
    intro j
    induction j with
    | zero => intro k hk; exact (hanti hk).trans (by simp [hn])
    | succ j ih =>
      intro k hk
      refine (c1 k).trans (sup_le le_rfl ((ih (k + 1) (by omega)).trans ?_))
      exact Submodule.span_mono fun x hx => ⟨hx.1, hanti (by omega) hx.2⟩
  exact c2 n k (by omega)

end Algebra

section Roots
variable {N : ℕ} (R : Finset (Fin N × Fin N))

def Deep (k : ℕ) : Fin N → Fin N → Prop :=
  Nat.rec (fun a c => (a, c) ∈ R) (fun _ D a c => ∃ b, (a, b) ∈ R ∧ D b c) k

variable {R}

theorem Deep.mem (ht : ∀ a b c : Fin N, (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R) :
    ∀ k a c, Deep R k a c → (a, c) ∈ R
  | 0, _, _, h => h
  | k + 1, a, c, ⟨b, h1, h2⟩ => ht a b c h1 (Deep.mem ht k b c h2)

theorem Deep.of_succ (ht : ∀ a b c : Fin N, (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R) :
    ∀ k a c, Deep R (k + 1) a c → Deep R k a c
  | 0, a, c, h => Deep.mem ht 1 a c h
  | k + 1, _, c, ⟨b, h1, h2⟩ => ⟨b, h1, Deep.of_succ ht k b c h2⟩

theorem Deep.trans (j : ℕ) (b c : Fin N) (h : Deep R j b c) :
    ∀ i a, Deep R i a b → Deep R (i + j + 1) a c
  | 0, a, h' => by rw [Nat.zero_add]; exact ⟨b, h', h⟩
  | i + 1, a, ⟨d, h1, h2⟩ => by
      rw [show i + 1 + j + 1 = (i + j + 1) + 1 by omega]
      exact ⟨d, h1, Deep.trans j b c h i d h2⟩

theorem Deep.lt (hl : ∀ q ∈ R, q.1 < q.2) : ∀ k a c, Deep R k a c → (a : ℕ) + k < c
  | 0, a, c, h => hl (a, c) h
  | k + 1, a, c, ⟨b, h1, h2⟩ => by
      have := Deep.lt hl k b c h2
      have : (a : ℕ) < b := hl (a, b) h1
      omega

variable (R) (ι : Type)

def deepSub (k : ℕ) : Submodule ℝ (ι → Matrix (Fin N) (Fin N) ℂ) where
  carrier := {x | ∀ v a c, ¬ Deep R k a c → x v a c = 0}
  add_mem' := fun hx hy v a c h => by simp [hx v a c h, hy v a c h]
  zero_mem' := fun _ _ _ _ => rfl
  smul_mem' := fun r x hx v a c h => by simp [hx v a c h]

def rootMat : (ι → R → ℂ) →ₗ[ℝ] (ι → Matrix (Fin N) (Fin N) ℂ) where
  toFun x := fun v => Matrix.of fun i j => if h : (i, j) ∈ R then x v ⟨(i, j), h⟩ else 0
  map_add' x y := by ext v i j; by_cases h : (i, j) ∈ R <;> simp [h]
  map_smul' r x := by ext v i j; by_cases h : (i, j) ∈ R <;> simp [h]

variable {R ι}

theorem deepSub_mul (i j : ℕ) (x y : ι → Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ deepSub R ι i)
    (hy : y ∈ deepSub R ι j) : x * y ∈ deepSub R ι (i + j + 1) := by
  intro v a c h
  rw [Pi.mul_apply, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h1 : Deep R i a b
  · rw [hy v b c fun h2 => h (Deep.trans j b c h2 i a h1), mul_zero]
  · rw [hx v a b h1, zero_mul]

theorem deepSub_gen [Fintype ι] (hl : ∀ q ∈ R, q.1 < q.2) (k : ℕ) :
    deepSub R ι (k + 1) ≤ Submodule.span ℝ
      {z | ∃ x ∈ deepSub R ι 0, ∃ y ∈ deepSub R ι k, z = x * y - y * x} := by
  intro x hx
  have : x = ∑ v, ∑ a, ∑ c, Pi.single v (Matrix.single a c (x v a c)) := by
    ext v : 1
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single v (fun w _ hw => by simp [Pi.single_eq_of_ne hw.symm]) (by simp)]
    simpa using Matrix.matrix_eq_sum_single (x v)
  rw [this]
  refine Submodule.sum_mem _ fun v _ => Submodule.sum_mem _ fun a _ =>
    Submodule.sum_mem _ fun c _ => ?_
  by_cases h : Deep R (k + 1) a c
  · have hac := Deep.lt hl _ _ _ h
    obtain ⟨b, h1, h2⟩ := h
    have hs : ∀ k a c z, Deep R k a c →
        (Pi.single v (Matrix.single a c z) : ι → Matrix (Fin N) (Fin N) ℂ) ∈ deepSub R ι k := by
      intro k a c z h w a' c' h'
      by_cases hw : w = v
      · subst hw
        rw [Pi.single_eq_same, Matrix.single_apply_of_ne]
        rintro ⟨rfl, rfl⟩; exact h' h
      · simp [Pi.single_eq_of_ne hw]
    refine Submodule.subset_span ⟨_, hs 0 a b (x v a c) h1, _, hs k b c 1 h2, ?_⟩
    have hca : c ≠ a := by rintro rfl; omega
    rw [← Pi.single_mul, ← Pi.single_mul, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne _ _ _ _ hca]
    simp
  · simp [hx v a c h]

theorem expT_sub_mem (hl : ∀ q ∈ R, q.1 < q.2)
    (hanti : Antitone (deepSub R ι)) (j : ℕ) (x y : ι → Matrix (Fin N) (Fin N) ℂ)
    (hx : x ∈ deepSub R ι 0) (hy : y ∈ deepSub R ι 0) (h : x - y ∈ deepSub R ι j) :
    (fun v => expT (x v)) - (fun v => expT (y v)) - (x - y) ∈ deepSub R ι (j + 1) := by
  by_cases hN : N < 2
  · have h0 : ∀ z ∈ deepSub R ι 0, z = 0 := fun z hz => by
      ext v a c
      refine hz v a c fun h => ?_
      have := Deep.lt hl _ _ _ h
      omega
    rw [h0 x hx, h0 y hy]; simp
  · have he : ∀ z : ι → Matrix (Fin N) (Fin N) ℂ, (fun v => expT (z v)) =
        ∑ i ∈ Finset.range (N - 2 + 2), ((i.factorial : ℝ))⁻¹ • z ^ i := fun z => by
      ext v : 1
      rw [show N - 2 + 2 = N by omega, expT, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Pi.pow_apply, ← Complex.coe_smul]; simp
    rw [he, he]
    exact trunc_sub_mem _ hanti deepSub_mul hx hy h _

end Roots

theorem cover : ∀ (ι : Type) [Fintype ι] (N : ℕ) (R : Finset (Fin N × Fin N)) (Λ : Submodule ℤ (ι → R → ℂ)) (Ω₀ : Set (ι → R → ℂ)), (∀ q ∈ R, q.1 < q.2) → (∀ a b c : Fin N, (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R) → MeasurableSet Ω₀ → MeasureTheory.IsAddFundamentalDomain Λ Ω₀ MeasureTheory.volume → MeasureTheory.volume Ω₀ ≠ ⊤ → DiscreteTopology Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ z ∈ Λ, ∀ v, expT (ofRoots R (x v) - 1) * expT (ofRoots R (y v) - 1) = expT (ofRoots R (z v) - 1)) → ∃ Ω : Set (ι → R → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω = MeasureTheory.volume Ω₀ ∧ ∀ c : ι → R → ℂ, ∃ x ∈ Λ, (fun v (q : R) => (expT (ofRoots R (x v) - 1) * ofRoots R (c v) : Matrix (Fin N) (Fin N) ℂ) q.1.1 q.1.2) ∈ Ω := by
  intro ι _ N R Λ Ω₀ hl ht _ hfd hfin hdisc hgr
  have hanti : Antitone (deepSub R ι) := antitone_nat_of_succ_le fun k x hx v a c h =>
    hx v a c fun h' => h (Deep.of_succ ht k a c h')
  have hn : deepSub R ι N = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    ext v a c
    refine hx v a c fun h => ?_
    have := Deep.lt hl _ _ _ h
    omega
  set L := rootMat R ι with hL
  let π : (ι → Matrix (Fin N) (Fin N) ℂ) → (ι → R → ℂ) := fun a v q => a v q.1.1 q.1.2
  let e : (ι → Matrix (Fin N) (Fin N) ℂ) → (ι → Matrix (Fin N) (Fin N) ℂ) := fun a v => expT (a v)
  have hLof : ∀ x v, ofRoots R (x v) = 1 + L x v := fun x v => by
    ext i j
    by_cases h : (i, j) ∈ R
    · have : i ≠ j := (hl _ h).ne
      simp [ofRoots, hL, rootMat, h, this]
    · simp [ofRoots, hL, rootMat, h, Matrix.one_apply]
  have hL0 : ∀ x, L x ∈ deepSub R ι 0 := fun x v a c h => by
    have : (a, c) ∉ R := h
    simp [hL, rootMat, this]
  have hπL : ∀ x, π (L x) = x := fun x => by ext v q; simp [π, hL, rootMat]
  have hLπ : ∀ a ∈ deepSub R ι 0, L (π (1 + a)) = a := fun a ha => by
    ext v i j
    by_cases h : (i, j) ∈ R
    · have : i ≠ j := (hl _ h).ne
      simp [π, hL, rootMat, h, this]
    · simp [hL, rootMat, h, ha v i j h]
  have hinj : Function.Injective L := Function.LeftInverse.injective hπL
  have he0 : e 0 = 1 := by
    ext v : 1
    rcases N with _ | N
    · exact Subsingleton.elim _ _
    · simp [e, expT, Finset.sum_range_succ']
  have he : ∀ j x y, x ∈ deepSub R ι 0 → y ∈ deepSub R ι 0 → x - y ∈ deepSub R ι j →
      e x - e y - (x - y) ∈ deepSub R ι (j + 1) := expT_sub_mem hl hanti
  have : (volume : Measure (R → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (ι → R → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have he1 : ∀ j x, x ∈ deepSub R ι j → e x - 1 - x ∈ deepSub R ι (j + 1) := fun j x hx => by
    have := he j x 0 (hanti (Nat.zero_le _) hx) (Submodule.zero_mem _) (by simpa using hx)
    rwa [he0, sub_zero] at this
  have hgr' : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ z ∈ Λ, e (L x) * e (L y) = e (L z) := fun x hx y hy => by
    obtain ⟨z, hz, h⟩ := hgr x hx y hy
    exact ⟨z, hz, funext fun v => by simpa [hLof] using h v⟩
  have hspan := span_eq_top volume Λ Ω₀ hfd hfin
  have hrat := rational (deepSub R ι) hanti deepSub_mul N hn (deepSub_gen hl) e he0 he
    (Λ.map (L.restrictScalars ℤ)) (by rintro _ ⟨x, -, rfl⟩; exact hL0 x)
    (fun a ha => by
      rw [← hLπ a ha]
      exact Submodule.apply_mem_span_image_of_mem_span L (s := (Λ : Set (ι → R → ℂ))) (hspan ▸ Submodule.mem_top))
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, h⟩ := hgr' x hx y hy
      exact ⟨_, ⟨z, hz, rfl⟩, h⟩)
  have hLφ : ∀ x c, L (π (e (L x) * (1 + L c))) = e (L x) * (1 + L c) - 1 := fun x c => by
    have h1 : e (L x) - 1 ∈ deepSub R ι 0 := by
      simpa using (deepSub R ι 0).add_mem (hanti (Nat.zero_le _) (he1 0 _ (hL0 x))) (hL0 x)
    have h2 : e (L x) * (1 + L c) - 1 ∈ deepSub R ι 0 := by
      have : e (L x) * (1 + L c) - 1 = (e (L x) - 1) + (e (L x) - 1) * L c + L c := by noncomm_ring
      rw [this]
      exact Submodule.add_mem _ (Submodule.add_mem _ h1
        (hanti (Nat.zero_le _) (deepSub_mul _ _ _ _ h1 (hL0 c)))) (hL0 c)
    simpa using hLπ _ h2
  obtain ⟨Ω, h1, h2, h3⟩ := exists_cover volume Λ Ω₀ hfd (fun k => (deepSub R ι k).comap L) N
    (eq_top_iff.2 fun x _ => hL0 x) (by simp [hn, LinearMap.ker_eq_bot.2 hinj])
    (fun i j hij => Submodule.comap_mono (hanti hij))
    (fun k x hx => by
      refine (Submodule.apply_mem_span_image_iff_mem_span hinj).1 (Submodule.span_mono ?_ (hrat k hx))
      rintro _ ⟨⟨y, hy, rfl⟩, hy'⟩
      exact ⟨y, ⟨hy, hy'⟩, rfl⟩)
    (fun x c => π (e (L x) * (1 + L c)))
    (fun k x _ hx c => by
      rw [Submodule.mem_comap, map_sub, map_sub, hLφ]
      have : e (L x) * (1 + L c) - 1 - L c - L x =
          (e (L x) - 1 - L x) + (e (L x) - 1 - L x) * L c + L x * L c := by noncomm_ring
      rw [this]
      exact Submodule.add_mem _ (Submodule.add_mem _ (he1 k _ hx)
        (hanti (by omega) (deepSub_mul _ _ _ _ (he1 k _ hx) (hL0 c))))
        (deepSub_mul _ _ _ _ hx (hL0 c)))
    (fun x hx y hy => by
      obtain ⟨z, hz, h⟩ := hgr' x hx y hy
      refine ⟨z, hz, fun c => ?_⟩
      simp only [hLφ, add_sub_cancel, ← mul_assoc, h])
  refine ⟨Ω, h1, h2, fun c => ?_⟩
  obtain ⟨x, hx, h⟩ := h3 c
  refine ⟨x, hx, ?_⟩
  simpa [hLof, π, e] using h

end GlobalTheory.LoopV.Cover
