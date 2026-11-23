import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas

namespace GlobalTheory.FdTransfer

theorem isFundamentalDomain_inclusion_image
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N Q R : Subgroup G) [Countable R] (hN : IsClosed (N : Set G))
    (hcov : ∀ h ∈ Q ⊔ N, ∃ r ∈ R, r * h ∈ N) (νN : Measure N) (ν : Measure ↥(Q ⊔ N))
    (hmass : ∀ A : Set N, ν (Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) '' A) = νN A)
    (hinv : ∀ h : ↥(Q ⊔ N), MeasurePreserving (h * ·) ν ν)
    (E : Set N) (hE : IsFundamentalDomain (R.subgroupOf N) E νN) :
    IsFundamentalDomain (R.subgroupOf (Q ⊔ N))
      (Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) '' E) ν := by
  set ι := Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) with hι
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective _
  haveI : Countable ↥(R.subgroupOf (Q ⊔ N)) := by
    refine Function.Injective.countable (f := fun g : ↥(R.subgroupOf (Q ⊔ N)) =>
      (⟨((g : ↥(Q ⊔ N)) : G), Subgroup.mem_subgroupOf.mp g.2⟩ : R)) ?_
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    have h := congrArg Subtype.val hab
    exact h
  have himg : ∀ T : Set N, MeasurableSet T → MeasurableSet (ι '' T) := by
    intro T hT
    have h1 : MeasurableSet (((↑) : N → G) '' T) :=
      (MeasurableEmbedding.subtype_coe hN.measurableSet).measurableSet_image' hT
    have h2 : ι '' T = ((↑) : ↥(Q ⊔ N) → G) ⁻¹' (((↑) : N → G) '' T) := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
      · rintro ⟨n, hn, hnx⟩
        exact ⟨n, hn, Subtype.ext hnx⟩
    rw [h2]
    exact measurable_subtype_coe h1
  have hqmp : ∀ g : ↥(R.subgroupOf (Q ⊔ N)),
      Measure.QuasiMeasurePreserving ((g • ·) : ↥(Q ⊔ N) → ↥(Q ⊔ N)) ν ν :=
    fun g => (hinv (g : ↥(Q ⊔ N))).quasiMeasurePreserving
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ hqmp
  ·
    obtain ⟨T, hTE, hT, hTae⟩ := hE.nullMeasurableSet.exists_measurable_subset_ae_eq
    have hdiff : νN (E \ T) = 0 := (ae_eq_set.mp hTae).2
    refine (himg T hT).nullMeasurableSet.congr ?_
    rw [ae_eq_set]
    constructor
    · rw [Set.diff_eq_empty.mpr (Set.image_mono hTE)]; simp
    · rw [← Set.image_diff hιinj, hmass]; exact hdiff
  ·
    set B : Set N := {n | ¬ ∃ l : ↥(R.subgroupOf N), l • n ∈ E} with hB
    have hB0 : νN B = 0 := by
      have := hE.ae_covers
      rw [ae_iff] at this
      exact this
    have hιB : ∀ᵐ y ∂ν, y ∉ ι '' B := by
      rw [ae_iff]; simp only [not_not, Set.setOf_mem_eq]; rw [hmass]; exact hB0
    have hall : ∀ᵐ x ∂ν, ∀ r : ↥(R.subgroupOf (Q ⊔ N)), (r • x) ∉ ι '' B := by
      rw [ae_all_iff]
      intro r
      exact (hqmp r).ae hιB
    filter_upwards [hall] with x hx
    obtain ⟨r, hrR, hrN⟩ := hcov x x.2
    have hrQN : r ∈ Q ⊔ N := by
      have : r = (r * x) * (x : G)⁻¹ := by group
      rw [this]
      exact (Q ⊔ N).mul_mem (le_sup_right (a := Q) hrN) ((Q ⊔ N).inv_mem x.2)
    let rr : ↥(R.subgroupOf (Q ⊔ N)) := ⟨⟨r, hrQN⟩, Subgroup.mem_subgroupOf.mpr hrR⟩
    let n : N := ⟨r * x, hrN⟩
    have hrx : rr • x = ι n := Subtype.ext rfl
    have hn : n ∉ B := fun hnB => hx rr ⟨n, hnB, hrx.symm⟩
    simp only [hB, Set.mem_setOf_eq, not_not] at hn
    obtain ⟨l, hl⟩ := hn
    let l' : ↥(R.subgroupOf (Q ⊔ N)) := ⟨ι (l : N), Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mp l.2)⟩
    refine ⟨l' * rr, l • n, hl, ?_⟩
    apply Subtype.ext
    show ((l : N) : G) * (r * x) = ((l : N) : G) * r * x
    rw [mul_assoc]
  ·
    intro g hg
    show ν (g • (ι '' E) ∩ ι '' E) = 0
    by_cases hgN : ((g : ↥(Q ⊔ N)) : G) ∈ N
    · let l : ↥(R.subgroupOf N) := ⟨⟨_, hgN⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mp g.2)⟩
      have hl : l ≠ 1 := by
        intro h
        apply hg
        have := congrArg (fun z : ↥(R.subgroupOf N) => ((z : N) : G)) h
        apply Subtype.ext; apply Subtype.ext
        exact this
      have hlE : νN (l • E ∩ E) = 0 := by
        have := hE.aedisjoint hl
        simpa [Function.onFun, AEDisjoint] using this
      refine measure_mono_null ?_ (by rw [hmass]; exact hlE)
      intro y hy
      obtain ⟨hy1, n', hn'E, hy2⟩ := hy
      rw [Set.mem_smul_set] at hy1
      obtain ⟨x, ⟨n, hnE, rfl⟩, hxy⟩ := hy1
      have key : ι (l • n) = g • ι n := Subtype.ext rfl
      have hln : l • n = n' := hιinj (key.trans (hxy.trans hy2.symm))
      refine ⟨l • n, ⟨Set.smul_mem_smul_set hnE, hln ▸ hn'E⟩, key.trans hxy⟩
    · refine measure_mono_null (t := ∅) ?_ measure_empty
      rintro y ⟨hy1, n', hn'E, hy2⟩
      rw [Set.mem_smul_set] at hy1
      obtain ⟨x, ⟨n, hnE, rfl⟩, hxy⟩ := hy1
      apply hgN
      have h1 : ((g : ↥(Q ⊔ N)) : G) * n = n' :=
        (congrArg (fun z : ↥(Q ⊔ N) => (z : G)) (hxy.trans hy2.symm))
      have h2 : ((g : ↥(Q ⊔ N)) : G) = n' * (n : G)⁻¹ := by rw [← h1]; group
      rw [h2]
      exact N.mul_mem n'.2 (N.inv_mem n.2)

end GlobalTheory.FdTransfer
