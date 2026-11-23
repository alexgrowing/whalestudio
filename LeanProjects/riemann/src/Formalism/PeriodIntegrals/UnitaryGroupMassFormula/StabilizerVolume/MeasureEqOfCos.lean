import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.CosDens

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter

section CosMeas

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in

def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem isOpen_thick (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have e : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x
    simp [thick]
  rw [e]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)

theorem measure_thick_eq (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  classical

  have hfib : ∀ c : X ⧸ Λ, m1 (((↑) : X → X ⧸ Λ) ⁻¹' {c}) = m2 (((↑) : X → X ⧸ Λ) ⁻¹' {c}) ∧
      MeasurableSet (((↑) : X → X ⧸ Λ) ⁻¹' {c}) := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    have e : ((↑) : X → X ⧸ Λ) ⁻¹' {(y : X ⧸ Λ)} = {z | z - y ∈ Λ} := by
      ext z
      simp [QuotientAddGroup.eq_iff_sub_mem]
    rw [e]
    exact ⟨h y, (hΛ.preimage (continuous_id.sub continuous_const)).measurableSet⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : S => {z : X | z - (s : X) ∈ Λ})
    (fun s => hΛ.preimage (continuous_id.sub continuous_const))
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, by simp⟩)
  have hT : thick S Λ = ⋃ c ∈ t.image (fun s : S => ((s : X) : X ⧸ Λ)),
      ((↑) : X → X ⧸ Λ) ⁻¹' {c} := by
    ext x
    simp only [thick, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_singleton_iff,
      Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨s', hs't, hss'⟩ := mem_iUnion₂.mp (ht hs)
      refine ⟨((s' : X) : X ⧸ Λ), ⟨s', hs't, rfl⟩, ?_⟩
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have e : x - (s' : X) = (x - s) + (s - s') := by abel
      rw [e]
      exact Λ.add_mem hxs hss'
    · rintro ⟨c, ⟨s', _, rfl⟩, hx⟩
      exact ⟨s', s'.2, (QuotientAddGroup.eq_iff_sub_mem).mp hx⟩
  rw [hT, measure_biUnion_finset, measure_biUnion_finset]
  · exact Finset.sum_congr rfl fun c _ => (hfib c).1
  all_goals first
    | exact fun c _ c' _ hne => (Set.disjoint_singleton.mpr hne).preimage _
    | exact fun c _ => (hfib c).2

omit [MeasurableSpace X] [OpensMeasurableSpace X] in

theorem iInter_thick (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx
    by_contra hxS
    have hN : (fun u => x - u) ⁻¹' Sᶜ ∈ 𝓝 (0 : X) := by
      apply (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
      simpa using hSc.isOpen_compl.mem_nhds hxS
    obtain ⟨n, hn⟩ := hb _ hN
    obtain ⟨s, hs, hxs⟩ := hx n
    have hmem := hn hxs
    simp only [mem_preimage, mem_compl_iff, sub_sub_cancel] at hmem
    exact hmem hs
  · intro hx n
    exact ⟨x, hx, by simp⟩

theorem measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hmono : Antitone fun n => thick S (Λ n) := by
    intro a c hac x hx
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hs, hanti hac hxs⟩
  have hnull : ∀ (μ : Measure X) n, NullMeasurableSet (thick S (Λ n)) μ := fun μ n =>
    (isOpen_thick S (Λ n) (hΛo n)).measurableSet.nullMeasurableSet
  have heq : ∀ n, m1 (thick S (Λ n)) = m2 (thick S (Λ n)) := fun n =>
    measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS
  rw [← iInter_thick S hSc Λ hb, hmono.measure_iInter (hnull m1) ⟨0, measure_ne_top _ _⟩,
    hmono.measure_iInter (hnull m2) ⟨0, by rw [← heq 0]; exact measure_ne_top _ _⟩]
  simp only [heq]

end CosMeas

theorem cosDens_holds : CosDens := by
  unfold CosDens
  intro X _ _ _ _ _ _ ν m _ _ H hHo _ hanti hb c0 κ hm0 hcos S hS
  have hle : ∀ n, H n ≤ H 0 := fun n => hanti (Nat.zero_le n)
  have hcos' : ∀ n y, m {z | z - y ∈ H n} = ((κ • ν).restrict {z | z - c0 ∈ H 0}) {z | z - y ∈ H n} := by
    intro n y
    have hmeas : MeasurableSet {z : X | z - y ∈ H n} :=
      ((hHo n).preimage (continuous_id.sub continuous_const)).measurableSet
    rw [Measure.restrict_apply hmeas, Measure.smul_apply, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z : X | z - y ∈ H n} ∩ {z | z - c0 ∈ H 0} = {z | z - y ∈ H n} := by
        apply inter_eq_left.mpr
        intro z hz
        have e : z - c0 = (z - y) + (y - c0) := by abel
        show z - c0 ∈ H 0
        rw [e]
        exact (H 0).add_mem (hle n hz) hy
      rw [hsub]
      exact hcos n y hy
    ·
      have hout : ∀ z, z - y ∈ H n → z - c0 ∉ H 0 := by
        intro z hz hz0
        apply hy
        have e : y - c0 = (z - c0) - (z - y) := by abel
        rw [e]
        exact (H 0).sub_mem hz0 (hle n hz)
      have hempty : {z : X | z - y ∈ H n} ∩ {z | z - c0 ∈ H 0} = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact hout z
      rw [hempty, measure_empty, mul_zero]
      exact measure_mono_null (fun z hz => hout z hz) hm0
  rw [measure_eq_of_cos m _ H hHo hanti hb hcos' S hS hS.isClosed,
    Measure.restrict_apply hS.isClosed.measurableSet, Measure.smul_apply, smul_eq_mul]

end PI.VolStabS
