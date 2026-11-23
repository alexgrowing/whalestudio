import Mathlib

namespace GroundTheory.Automorphic

open Set Filter Topology Uniformity UniformSpace Function

structure MeasurablePartition (X : Type*) [MeasurableSpace X] where

  n : ℕ

  E : ℕ → Set X
  measurableSet : ∀ i, MeasurableSet (E i)
  disjoint : Pairwise (Disjoint on E)
  exists_mem : ∀ x, ∃ i < n, x ∈ E i

namespace MeasurablePartition

variable {X : Type*} [MeasurableSpace X]

instance : Inhabited (MeasurablePartition X) where
  default :=
    { n := 1
      E := fun i => if i = 0 then univ else ∅
      measurableSet := fun i => by split_ifs <;> simp
      disjoint := by
        intro i j hij
        simp only [Function.onFun]
        by_cases hi : i = 0
        · have hj : j ≠ 0 := fun h => hij (hi.trans h.symm)
          simp [hj]
        · simp [hi]
      exists_mem := fun x => ⟨0, Nat.one_pos, by simp⟩ }

variable (p : MeasurablePartition X)

theorem eq_empty_of_le {i : ℕ} (hi : p.n ≤ i) : p.E i = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨j, hj, hxj⟩ := p.exists_mem x
  exact Set.disjoint_left.1 (p.disjoint (show j ≠ i by omega)) hxj hx

theorem biUnion_eq : ⋃ i ∈ Finset.range p.n, p.E i = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨i, hi, hx⟩ := p.exists_mem x
  exact mem_biUnion (Finset.mem_range.2 hi) hx

open Classical in

noncomputable def index (x : X) : ℕ := Nat.find (p.exists_mem x)

theorem index_lt (x : X) : p.index x < p.n := by
  classical exact (Nat.find_spec (p.exists_mem x)).1

theorem mem_index (x : X) : x ∈ p.E (p.index x) := by
  classical exact (Nat.find_spec (p.exists_mem x)).2

theorem index_eq_iff {x : X} {i : ℕ} : p.index x = i ↔ x ∈ p.E i := by
  refine ⟨fun h => h ▸ p.mem_index x, fun h => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 (p.disjoint hne) (p.mem_index x) h

theorem measurable_index : Measurable p.index := by
  refine measurable_to_countable' fun i => ?_
  have : p.index ⁻¹' {i} = p.E i := by ext x; simp [p.index_eq_iff]
  rw [this]
  exact p.measurableSet i

def IsFine (V : SetRel X X) : Prop := ∀ i, ∀ x ∈ p.E i, ∀ y ∈ p.E i, (x, y) ∈ V

variable {p} in
theorem IsFine.mono {V W : SetRel X X} (h : p.IsFine V) (hVW : V ⊆ W) : p.IsFine W :=
  fun i x hx y hy => hVW (h i x hx y hy)

theorem exists_isFine [UniformSpace X] [CompactSpace X] [OpensMeasurableSpace X] {V : SetRel X X}
    (hV : V ∈ 𝓤 X) : ∃ p : MeasurablePartition X, p.IsFine V := by
  obtain ⟨W, hW, hWo, hWs, hWV⟩ := comp_open_symm_mem_uniformity_sets hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ball x W)
    (fun x => isOpen_ball x hWo) (fun x _ => mem_iUnion.2 ⟨x, mem_ball_self x hW⟩)
  let L := t.toList
  let F : ℕ → Set X := fun i => if h : i < L.length then ball (L.get ⟨i, h⟩) W else ∅
  have hF : ∀ i, MeasurableSet (F i) := by
    intro i
    simp only [F]
    split_ifs
    · exact (isOpen_ball _ hWo).measurableSet
    · exact MeasurableSet.empty
  have hFn : ∀ i, L.length ≤ i → F i = ∅ := by
    intro i hi
    simp only [F, dif_neg (not_lt.2 hi)]
  refine ⟨⟨L.length, disjointed F, MeasurableSet.disjointed hF, disjoint_disjointed F, ?_⟩, ?_⟩
  · intro x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 (Finset.mem_toList.2 hy)
    have hxF : x ∈ F i := by
      show x ∈ (if h : (i : ℕ) < L.length then ball (L.get ⟨i, h⟩) W else ∅)
      rw [dif_pos i.2]
      exact (show L.get ⟨i, i.2⟩ = y from hi) ▸ hxy
    have hx : x ∈ ⋃ j, disjointed F j := by
      rw [iUnion_disjointed]
      exact mem_iUnion.2 ⟨i, hxF⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    refine ⟨j, ?_, hj⟩
    by_contra hjn
    have := disjointed_subset F j hj
    rw [hFn j (not_lt.1 hjn)] at this
    exact this
  · intro i x hx y hy
    have hxF := disjointed_subset F i hx
    have hyF := disjointed_subset F i hy
    simp only [F] at hxF hyF
    split_ifs at hxF hyF with h
    · have := hWs
      have hx' : L.get ⟨i, h⟩ ∈ ball x W := mem_ball_symmetry.1 hxF
      exact hWV (mem_ball_comp hx' hyF)
    · exact hxF.elim

end MeasurablePartition

open MeasurablePartition

section Filter

variable (X : Type*) [UniformSpace X]

def fineFilter : Filter (SetRel X X) := (𝓤 X).smallSets ⊓ 𝓟 {V | V ∈ 𝓤 X}

instance : (fineFilter X).NeBot := by
  refine Filter.inf_principal_neBot_iff.2 fun U hU => ?_
  obtain ⟨t, ht, htU⟩ := (hasBasis_smallSets _).mem_iff.1 hU
  exact ⟨t, htU (mem_powerset subset_rfl), ht⟩

variable {X}

theorem eventually_fineFilter {W : SetRel X X} (hW : W ∈ 𝓤 X) :
    ∀ᶠ V in fineFilter X, V ⊆ W ∧ V ∈ 𝓤 X := by
  have h1 : ∀ᶠ V in (𝓤 X).smallSets, V ⊆ W := eventually_smallSets_subset.2 hW
  exact (h1.filter_mono inf_le_left).and (eventually_inf_principal.2 (Eventually.of_forall
    fun _ hV => hV))

variable [MeasurableSpace X] [CompactSpace X] [OpensMeasurableSpace X]

open Classical in

noncomputable def finePart (V : SetRel X X) : MeasurablePartition X :=
  if h : V ∈ 𝓤 X then (exists_isFine h).choose else default

theorem finePart_isFine {V : SetRel X X} (hV : V ∈ 𝓤 X) : (finePart V).IsFine V := by
  classical
  simp only [finePart, dif_pos hV]
  exact (exists_isFine hV).choose_spec

theorem eventually_finePart_isFine {W : SetRel X X} (hW : W ∈ 𝓤 X) :
    ∀ᶠ V in fineFilter X, (finePart V).IsFine W := by
  filter_upwards [eventually_fineFilter hW] with V hV
  exact (finePart_isFine hV.2).mono hV.1

end Filter

section Measurable

variable {X Y : Type*} [UniformSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [UniformSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]

theorem measurable_of_continuous_prod {β : Type*} [PseudoMetricSpace β] [MeasurableSpace β]
    [BorelSpace β] {k : X × Y → β} (hk : Continuous k) : Measurable k := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · intro s _
    rw [Set.eq_empty_of_isEmpty (k ⁻¹' s)]
    exact MeasurableSet.empty
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y₀⟩⟩
  · intro s _
    rw [Set.eq_empty_of_isEmpty (k ⁻¹' s)]
    exact MeasurableSet.empty
  have huc : UniformContinuous k := CompactSpace.uniformContinuous_of_continuous hk

  have hent : ∀ m : ℕ, ∃ u ∈ 𝓤 X, ∃ v ∈ 𝓤 Y, ∀ x x' y y', (x, x') ∈ u → (y, y') ∈ v →
      dist (k (x, y)) (k (x', y')) < 1 / (m + 1) := by
    intro m
    have h := huc (Metric.dist_mem_uniformity (by positivity : (0 : ℝ) < 1 / (m + 1)))
    obtain ⟨u, hu, v, hv, huv⟩ := entourageProd_subset h
    exact ⟨u, hu, v, hv, fun x x' y y' hx hy => huv (show ((x, y), (x', y')) ∈
      entourageProd u v from ⟨hx, hy⟩)⟩
  choose u hu v hv huv using hent
  let p : ℕ → MeasurablePartition X := fun m => (exists_isFine (hu m)).choose
  let q : ℕ → MeasurablePartition Y := fun m => (exists_isFine (hv m)).choose
  have hp : ∀ m, (p m).IsFine (u m) := fun m => (exists_isFine (hu m)).choose_spec
  have hq : ∀ m, (q m).IsFine (v m) := fun m => (exists_isFine (hv m)).choose_spec
  classical
  let rX : MeasurablePartition X → ℕ → X := fun P i => if h : (P.E i).Nonempty then h.some else x₀
  let rY : MeasurablePartition Y → ℕ → Y := fun P i => if h : (P.E i).Nonempty then h.some else y₀
  have hrX : ∀ P i x, x ∈ P.E i → rX P i ∈ P.E i := by
    intro P i x hx
    simp only [rX, dif_pos (show (P.E i).Nonempty from ⟨x, hx⟩)]
    exact Set.Nonempty.some_mem _
  have hrY : ∀ P i y, y ∈ P.E i → rY P i ∈ P.E i := by
    intro P i y hy
    simp only [rY, dif_pos (show (P.E i).Nonempty from ⟨y, hy⟩)]
    exact Set.Nonempty.some_mem _
  let kk : ℕ → X × Y → β := fun m z =>
    k (rX (p m) ((p m).index z.1), rY (q m) ((q m).index z.2))
  have hmeas : ∀ m, Measurable (kk m) := by
    intro m
    have h1 : Measurable fun z : X × Y => ((p m).index z.1, (q m).index z.2) :=
      ((p m).measurable_index.comp measurable_fst).prodMk
        ((q m).measurable_index.comp measurable_snd)
    exact (measurable_of_countable
      (fun ij : ℕ × ℕ => k (rX (p m) ij.1, rY (q m) ij.2))).comp h1
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun z => ?_)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun m hm => ?_⟩
  have hx := (p m).mem_index z.1
  have hy := (q m).mem_index z.2
  have h1 := hp m _ _ (hrX _ _ _ hx) _ hx
  have h2 := hq m _ _ (hrY _ _ _ hy) _ hy
  refine (huv m _ _ _ _ h1 h2).trans_le ?_ |>.trans hN
  gcongr

end Measurable

end GroundTheory.Automorphic
