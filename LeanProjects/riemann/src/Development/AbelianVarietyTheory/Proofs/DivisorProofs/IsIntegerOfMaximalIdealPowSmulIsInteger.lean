import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem isInteger_of_maximalIdeal_smul_isInteger (S : Type) [CommRing S] [IsRegularLocalRing S]
    (hdim : 2 ≤ ringKrullDim S) (c : FractionRing S)
    (hc : ∀ a ∈ maximalIdeal S, IsLocalization.IsInteger S (a • c)) :
    IsLocalization.IsInteger S c := by
  obtain ⟨hD, hI⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing S
  have hinj : Function.Injective (algebraMap S (FractionRing S)) := IsFractionRing.injective S (FractionRing S)
  by_cases hA : ∀ a ∈ maximalIdeal S, ∃ y ∈ maximalIdeal S, algebraMap S (FractionRing S) y = a • c
  ·
    let N : Submodule S (FractionRing S) := Submodule.map (Algebra.linearMap S (FractionRing S)) (maximalIdeal S)
    have hne : maximalIdeal S ≠ ⊥ := by
      intro h
      have hF : IsField S := (isField_iff_maximalIdeal_eq).2 h
      have := ringKrullDim_eq_zero_of_isField hF
      rw [this] at hdim
      exact absurd hdim (by decide)
    have hN : N ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : Algebra.linearMap S (FractionRing S) x ∈ N := Submodule.mem_map_of_mem hx
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact hinj (by simpa using this)
    have hFG : N.FG := Submodule.FG.map _ (IsNoetherian.noetherian _)
    have hint : IsIntegral S c := by
      refine isIntegral_of_smul_mem_submodule N hN hFG c ?_
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨y, hy, hy'⟩ := hA a ha
      refine Submodule.mem_map.2 ⟨y, hy, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      rw [hy', Algebra.smul_def, mul_comm]
    exact (IsIntegrallyClosed.isIntegral_iff).1 hint
  · exfalso
    push_neg at hA
    obtain ⟨a, ha, hy⟩ := hA
    obtain ⟨y, hy'⟩ := hc a ha
    have hyu : y ∉ maximalIdeal S := fun h => hy y h hy'
    have hyunit : IsUnit y := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hyu
    have hspan : maximalIdeal S = Ideal.span {a} := by
      apply le_antisymm
      · intro b hb
        obtain ⟨z, hz⟩ := hc b hb
        have key : b * y = a * z := by
          apply hinj
          rw [map_mul, map_mul, hy', hz, ← Algebra.smul_def, ← Algebra.smul_def, smul_comm]
        rw [Ideal.mem_span_singleton']
        obtain ⟨u, rfl⟩ := hyunit
        refine ⟨z * ↑u⁻¹, ?_⟩
        calc z * ↑u⁻¹ * a = (a * z) * ↑u⁻¹ := by ring
          _ = (b * ↑u) * ↑u⁻¹ := by rw [key]
          _ = b := by simp [mul_assoc]
      · rw [Ideal.span_le]
        simpa using ha
    have h1 : (maximalIdeal S).spanFinrank ≤ 1 := by
      rw [hspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton a)).trans ?_
      simp
    have h2 := ringKrullDim_le_spanFinrank_maximalIdeal S
    have h3 : ringKrullDim S ≤ 1 := h2.trans (by exact_mod_cast h1)
    have := hdim.trans h3
    exact absurd this (by decide)

theorem isInteger_of_maximalIdeal_pow_smul_isInteger :
    ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S →
      ∀ (k : ℕ) (c : FractionRing S), (∀ a ∈ maximalIdeal S ^ k,
        IsLocalization.IsInteger S (a • c)) → IsLocalization.IsInteger S c := by
  intro S _ _ hdim k
  induction k with
  | zero =>
    intro c hc
    simpa using hc 1 (by simp)
  | succ k ih =>
    intro c hc
    apply isInteger_of_maximalIdeal_smul_isInteger S hdim c
    intro a ha
    apply ih
    intro b hb
    rw [smul_smul]
    apply hc
    rw [pow_succ]
    exact Ideal.mul_mem_mul hb ha

end GlobalTheory
