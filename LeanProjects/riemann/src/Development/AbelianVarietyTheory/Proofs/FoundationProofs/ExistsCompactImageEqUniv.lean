import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2Cocompact

theorem isOpenMap_mk {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) :
    IsOpenMap (mk Γ) := by
  intro U hU
  have h : mk Γ ⁻¹' (mk Γ '' U) = ⋃ γ : Γ, (fun x => ((γ : G))⁻¹ * x) ⁻¹' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, e⟩
      obtain ⟨γ, rfl⟩ := mk_eq_iff.1 e
      exact ⟨γ, by simpa using hy⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨_, hγ, mk_eq_iff.2 ⟨γ, by simp⟩⟩
  refine isOpen_coinduced.2 ?_
  change IsOpen (mk Γ ⁻¹' (mk Γ '' U))
  rw [h]
  exact isOpen_iUnion fun γ => hU.preimage (by fun_prop)

theorem exists_compact_image_eq_univ {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (Γ : Subgroup G) [CompactSpace (Quot Γ)] :
    ∃ C : Set G, IsCompact C ∧ mk Γ '' C = Set.univ := by
  classical
  choose K hK hK' using fun x : G => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : G => mk Γ '' interior (K x))
    (fun x => isOpenMap_mk Γ _ isOpen_interior) (fun q _ => by
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      exact Set.mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hK' x), rfl⟩)
  refine ⟨⋃ x ∈ t, K x, t.isCompact_biUnion fun x _ => hK x, Set.eq_univ_of_forall fun q => ?_⟩
  obtain ⟨x, hx, y, hy, e⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
  exact ⟨y, Set.mem_iUnion₂.2 ⟨x, hx, interior_subset hy⟩, e⟩

theorem cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], CompactSpace (Quot Γ) → IsFiniteMeasure (quotMeasure Γ μ) ∧ (∃ C : Set G, IsCompact C ∧ mk Γ '' C = Set.univ) ∧ ∀ φ : G → ℂ, LeftInv Γ φ → Continuous φ → MemL2Quotient Γ μ φ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ hc
  obtain ⟨C, hC, hCe⟩ := exists_compact_image_eq_univ Γ
  have hfin : IsFiniteMeasure (quotMeasure Γ μ) :=
    ⟨(quotMeasure_le MeasurableSet.univ hCe.ge).trans_lt hC.measure_lt_top⟩
  refine ⟨hfin, ⟨C, hC, hCe⟩, fun φ hφ hcont => ⟨hφ, ?_⟩⟩
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  refine MemLp.of_bound ?_ B (Filter.Eventually.of_forall fun q => ?_)
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, hφ.lift_descend]
    exact hcont.aestronglyMeasurable
  · obtain ⟨x, hx, rfl⟩ := hCe.ge (Set.mem_univ q)
    rw [hφ.descend_mk]
    exact hB x hx

end GlobalTheory.AutomorphicL2Cocompact
