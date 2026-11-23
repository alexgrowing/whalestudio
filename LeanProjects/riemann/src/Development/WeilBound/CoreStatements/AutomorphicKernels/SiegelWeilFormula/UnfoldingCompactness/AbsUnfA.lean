import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PositivityTheory.SiegelWeilFormula.kunf

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] {lam : Measure V} [lam.IsAddHaarMeasure] {Λ : AddSubgroup V} [Countable Λ]
  {𝓖 : Set V}

omit [SecondCountableTopology V] in

theorem lintegral_fd_le (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (S : V → ℝ≥0∞)
    (hS : ∀ (ν : Λ) β, S (β + ν) = S β) {C : Set V} (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C) :
    ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in C, S β ∂lam := by
  rw [h𝓖.setLIntegral_eq_tsum' S C]
  have hsub : 𝓖 ⊆ ⋃ ν : Λ, (ν +ᵥ C) ∩ 𝓖 := by
    intro β hβ
    obtain ⟨ν, hν⟩ := hcov β
    refine Set.mem_iUnion.2 ⟨-ν, ?_, hβ⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    exact hν
  calc ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in ⋃ ν : Λ, (ν +ᵥ C) ∩ 𝓖, S β ∂lam := lintegral_mono_set hsub
    _ ≤ ∑' ν : Λ, ∫⁻ β in (ν +ᵥ C) ∩ 𝓖, S β ∂lam := lintegral_iUnion_le _ _
    _ = ∑' ν : Λ, ∫⁻ x in (ν +ᵥ C) ∩ 𝓖, S (-ν +ᵥ x) ∂lam := by
      refine tsum_congr fun ν => lintegral_congr fun x => ?_
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
      exact (hS (-ν) x).symm

omit [SecondCountableTopology V] in

theorem setIntegral_fd_eq_zero (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (g : V → ℂ)
    (hg : ∀ (ν : Λ) β, g (β + ν) = g β) (β₀ : V) (c : ℂ) (hc : c ≠ 1) (hβ₀ : ∀ β, g (β + β₀) = c * g β) :
    ∫ β in 𝓖, g β ∂lam = 0 := by
  have h1 : IsAddFundamentalDomain Λ ((-β₀) +ᵥ 𝓖) lam := h𝓖.vadd_of_comm (-β₀)
  have h2 : ∫ β in 𝓖, g β ∂lam = ∫ x in (-β₀) +ᵥ 𝓖, g (β₀ +ᵥ x) ∂lam := by
    rw [← (measurePreserving_vadd β₀ lam).setIntegral_image_emb (measurableEmbedding_const_vadd β₀)]
    congr 1
    rw [Set.image_vadd, vadd_vadd, add_neg_cancel, zero_vadd]
  have h3 : ∫ x in (-β₀) +ᵥ 𝓖, g (β₀ +ᵥ x) ∂lam = c * ∫ β in 𝓖, g β ∂lam := by
    have e : (fun x => g (β₀ +ᵥ x)) = fun x => c * g x := funext fun x => by
      rw [vadd_eq_add, add_comm, hβ₀]
    rw [e, h1.setIntegral_eq h𝓖 (fun ν x => by rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm, hg]),
      integral_const_mul]
  have h4 : (1 - c) * ∫ β in 𝓖, g β ∂lam = 0 := by
    rw [sub_mul, one_mul, ← h3, ← h2, sub_self]
  exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (Ne.symm hc))

end PositivityTheory.SiegelWeilFormula.kunf

end
