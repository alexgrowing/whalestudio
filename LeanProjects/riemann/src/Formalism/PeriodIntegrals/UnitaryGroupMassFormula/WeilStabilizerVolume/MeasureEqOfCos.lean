import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.CosDens

noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology Set Filter

section CosMeas

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in

def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem isOpen_thick (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x; simp [thick]
  rw [this]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)

theorem measure_thick_eq (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  have : DiscreteTopology (X ⧸ Λ) := QuotientAddGroup.discreteTopology hΛ
  let q : X → X ⧸ Λ := QuotientAddGroup.mk
  have hq : Continuous q := continuous_quot_mk
  have hfin : (q '' S).Finite := (hS.image hq).finite_of_discrete
  have hcos : ∀ y, q ⁻¹' {q y} = {z | z - y ∈ Λ} := by
    intro y
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq, q]
    exact QuotientAddGroup.eq_iff_sub_mem
  have hset : thick S Λ = ⋃ p ∈ hfin.toFinset, q ⁻¹' {p} := by
    ext x
    simp only [thick, mem_setOf_eq, mem_iUnion, Finite.mem_toFinset, mem_image, exists_prop]
    constructor
    · rintro ⟨s, hs, hx⟩
      refine ⟨q s, ⟨s, hs, rfl⟩, ?_⟩
      rw [hcos]
      exact hx
    · rintro ⟨p, ⟨s, hs, rfl⟩, hx⟩
      rw [hcos] at hx
      exact ⟨s, hs, hx⟩
  have hmeas : ∀ p : X ⧸ Λ, MeasurableSet (q ⁻¹' {p}) := fun p =>
    ((isOpen_discrete ({p} : Set (X ⧸ Λ))).preimage hq).measurableSet
  have hdisj : PairwiseDisjoint (↑hfin.toFinset : Set (X ⧸ Λ)) (fun p => q ⁻¹' {p}) :=
    fun p _ p' _ hne => (disjoint_singleton.2 hne).preimage q
  rw [hset, measure_biUnion_finset hdisj (fun p _ => hmeas p),
    measure_biUnion_finset hdisj (fun p _ => hmeas p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective p
  have := hcos y
  simp only [q] at this
  rw [this]
  exact h y

omit [MeasurableSpace X] [OpensMeasurableSpace X] in

theorem iInter_thick (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx
    rw [← hSc.closure_eq, mem_closure_iff_nhds]
    intro N hN
    have h0 : {d : X | x - d ∈ N} ∈ 𝓝 (0 : X) := by
      have hc : Continuous fun d : X => x - d := continuous_const.sub continuous_id
      have := hc.continuousAt (x := 0) (by simpa using hN)
      exact this
    obtain ⟨n, hn⟩ := hb _ h0
    obtain ⟨s, hs, hxs⟩ := hx n
    have := hn hxs
    simp only [mem_setOf_eq, sub_sub_cancel] at this
    exact ⟨s, this, hs⟩
  · intro hx n
    exact ⟨x, hx, by simp [(Λ n).zero_mem]⟩

theorem measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hA : Antitone fun n => thick S (Λ n) := by
    intro n k hnk
    rintro x ⟨s, hs, hx⟩
    exact ⟨s, hs, hanti hnk hx⟩
  have hm : ∀ n, NullMeasurableSet (thick S (Λ n)) m1 := fun n =>
    (isOpen_thick S _ (hΛo n)).measurableSet.nullMeasurableSet
  have hm2 : ∀ n, NullMeasurableSet (thick S (Λ n)) m2 := fun n =>
    (isOpen_thick S _ (hΛo n)).measurableSet.nullMeasurableSet
  have h0 := measure_thick_eq m1 m2 (Λ 0) (hΛo 0) (h 0) S hS
  rw [← iInter_thick S hSc Λ hb, hA.measure_iInter hm ⟨0, measure_ne_top _ _⟩,
    hA.measure_iInter hm2 ⟨0, h0 ▸ measure_ne_top _ _⟩]
  exact iInf_congr fun n => measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS

end CosMeas

theorem cosDens_holds : CosDens := by
  intro X _ _ _ _ _ _ ν m _ _ H hHo _ hHa hb c0 κ hCc hcos S hS
  set C : Set X := {z | z - c0 ∈ H 0} with hC
  have hCm : MeasurableSet C :=
    ((hHo 0).preimage (continuous_id.sub continuous_const)).measurableSet
  have key : ∀ n y, m {z | z - y ∈ H n} = (κ • ν.restrict C) {z | z - y ∈ H n} := by
    intro n y
    rw [Measure.smul_apply, Measure.restrict_apply' hCm, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z | z - y ∈ H n} ⊆ C := by
        intro z hz
        have := (H 0).add_mem (hHa (Nat.zero_le n) hz) hy
        simpa [hC, sub_add_sub_cancel] using this
      rw [Set.inter_eq_left.2 hsub]
      exact hcos n y hy
    · have hdis : {z | z - y ∈ H n} ∩ C = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hC, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro hz hzc
        apply hy
        have := (H 0).sub_mem hzc (hHa (Nat.zero_le n) hz)
        simpa [sub_sub_sub_cancel_left] using this
      rw [hdis, measure_empty, mul_zero]
      refine measure_mono_null (fun z hz => ?_) hCc
      intro hzc
      apply hy
      have := (H 0).sub_mem hzc (hHa (Nat.zero_le n) hz)
      simpa [sub_sub_sub_cancel_left] using this
  have := measure_eq_of_cos m (κ • ν.restrict C) H hHo hHa hb key S hS hS.isClosed
  rw [this, Measure.smul_apply, Measure.restrict_apply' hCm, smul_eq_mul]

end PI.VolStabW
