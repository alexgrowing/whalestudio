import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothPeriodicPartitionOfUnity
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

theorem periodic_cech_cocycle_smooth_coboundary : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i j, ContDiffOn ℝ ∞ (c i j) (U i ∩ U j)) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, c i j (z + l) = c i j z) → (∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k, c i j z + c j k z = c i k z) → ∃ b : ι → (Fin g → ℂ) → ℂ, (∀ i, ContDiffOn ℝ ∞ (b i) (U i) ∧ ∀ (l : Λ), ∀ z ∈ U i, b i (z + l) = b i z) ∧ ∀ i j, ∀ z ∈ U i ∩ U j, c i j z = b j z - b i z := by
  intro g Λ hΛ hspan ι U c hU hper hcov hc hcper hcoc
  obtain ⟨s, ρ, hρ, hsum⟩ :=
    exists_smooth_periodic_partition_of_unity g Λ hΛ hspan ι U hU hper hcov
  have hzero : ∀ k z, z ∉ U k → ρ k z = 0 := by
    intro k z hz
    by_contra h
    exact hz ((hρ k).2.2 (subset_tsupport _ (Function.mem_support.mpr h)))
  refine ⟨fun i z => ∑ k ∈ s, (ρ k z : ℂ) * c k i z, fun i => ⟨?_, ?_⟩, ?_⟩
  · refine ContDiffOn.sum (fun k _ => ?_)
    have hρc : ContDiff ℝ ∞ (fun z => (ρ k z : ℂ)) := ofRealCLM.contDiff.comp (hρ k).1
    apply contDiffOn_of_locally_contDiffOn
    intro x _
    by_cases hxk : x ∈ U k
    · refine ⟨U k, hU k, hxk, ?_⟩
      exact hρc.contDiffOn.mul ((hc k i).mono fun z hz => ⟨hz.2, hz.1⟩)
    · refine ⟨(tsupport (ρ k))ᶜ, (isClosed_tsupport _).isOpen_compl,
        fun h => hxk ((hρ k).2.2 h), ?_⟩
      refine (contDiffOn_const (c := (0 : ℂ))).congr fun z hz => ?_
      simp [image_eq_zero_of_notMem_tsupport hz.2]
  · intro l z hz
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hρ k).2.1 l z]
    by_cases hzk : z ∈ U k
    · rw [hcper k i l z ⟨hzk, hz⟩]
    · simp [hzero k z hzk]
  · intro i j z hz
    have hone : c i j z = ∑ k ∈ s, (ρ k z : ℂ) * c i j z := by
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum z]
      simp
    rw [hone, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hzk : z ∈ U k
    · rw [← hcoc k i j z ⟨⟨hzk, hz.1⟩, hz.2⟩]
      ring
    · simp [hzero k z hzk]

end GlobalTheory
