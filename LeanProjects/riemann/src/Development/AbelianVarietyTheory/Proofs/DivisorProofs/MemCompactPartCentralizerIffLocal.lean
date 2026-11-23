import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
open Filter GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.BCT

theorem mem_cptPart_iff_local (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type)
    [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)]
    (p : ∀ i, G →* H i) (KH : ∀ i, Subgroup (H i)) (T : Subgroup G) (TH : ∀ i, Subgroup (H i)) :
    (∀ i, Continuous (p i)) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) →
    (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) →
      IsCompact {x : G | ∀ i, p i x ∈ C i}) →
    (∀ i, IsCompact (KH i : Set (H i))) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) →
    (∀ i, ∀ a ∈ TH i, ∀ b ∈ TH i, a * b = b * a) →
    ∀ x, x ∈ cptPart T ↔ x ∈ T ∧ ∀ i, p i x ∈ cptPart (TH i) := by
  intro hp hcof hcpt hKH hT hcomm x
  constructor
  · intro hx
    have hle : cptPart T ≤ T ⊓ ⨅ i, (cptPart (TH i)).comap (p i) := by
      rw [cptPart, Subgroup.closure_le]
      intro t ht
      obtain ⟨htT, htc⟩ := ht
      rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_iInf]
      refine ⟨htT, fun i => ?_⟩
      rw [Subgroup.mem_comap]
      refine Subgroup.subset_closure (k := {s | s ∈ TH i ∧ IsCompact (closure (Subgroup.zpowers s : Set (H i)))})
        ⟨(hT t).1 htT i, ?_⟩
      have himc : IsCompact (p i '' closure (Subgroup.zpowers t : Set G)) := htc.image (hp i)
      refine himc.of_isClosed_subset isClosed_closure (closure_minimal ?_ himc.isClosed)
      rintro _ ⟨k, rfl⟩
      exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    have := hle hx
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap] at this
    exact this
  · rintro ⟨hxT, hxi⟩
    have hloc : ∀ i, IsCompact (closure (Subgroup.zpowers (p i x) : Set (H i))) := fun i =>
      (GlobalTheory.LocFinU.cptPart_subset_of_comm (TH i) (hcomm i) (hxi i)).2
    set C : ∀ i, Set (H i) := fun i => if p i x ∈ KH i then (KH i : Set (H i))
      else closure (Subgroup.zpowers (p i x) : Set (H i)) with hC
    have hCc : ∀ i, IsCompact (C i) := by
      intro i
      simp only [hC]
      split_ifs
      · exact hKH i
      · exact hloc i
    have hCf : ∀ᶠ i in cofinite, C i = KH i := by
      filter_upwards [hcof x] with i hi
      simp [hC, hi]
    have hS := hcpt C hCc hCf
    have hScl : IsClosed {y : G | ∀ i, p i y ∈ C i} := by
      have : {y : G | ∀ i, p i y ∈ C i} = ⋂ i, p i ⁻¹' C i := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => (hCc i).isClosed.preimage (hp i)
    have hsub : (Subgroup.zpowers x : Set G) ⊆ {y : G | ∀ i, p i y ∈ C i} := by
      rintro _ ⟨k, rfl⟩ i
      simp only [hC, map_zpow]
      split_ifs with h
      · exact (KH i).zpow_mem h k
      · exact subset_closure ⟨k, rfl⟩
    refine Subgroup.subset_closure (k := {s | s ∈ T ∧ IsCompact (closure (Subgroup.zpowers s : Set G))}) ⟨hxT, ?_⟩
    exact hS.of_isClosed_subset isClosed_closure (closure_minimal hsub hScl)

end GlobalTheory.BCT
