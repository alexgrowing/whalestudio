import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DPQuot

theorem quotient_subDPIdeal : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J),
    (∀ 𝔟 : Ideal B, δ.IsSubDPIdeal 𝔟 → ∃ δ' : DividedPowers (J.map (Ideal.Quotient.mk 𝔟)),
      IsDPMorphism δ δ' (Ideal.Quotient.mk 𝔟) ∧
      ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : B ⧸ 𝔟 →+* C),
        IsDPMorphism δ δ'' (g.comp (Ideal.Quotient.mk 𝔟)) → IsDPMorphism δ' δ'' g) ∧
    ∀ s : Set B, s ⊆ J →
      δ.IsSubDPIdeal (Ideal.span {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ x ∈ s, y = δ.dpow n x}) := by
  intro B _ J δ
  refine ⟨fun 𝔟 h𝔟 ↦ ?_, fun s hs ↦ ?_⟩
  · have hinf : δ.IsSubDPIdeal (𝔟 ⊓ J) := by
      rw [inf_eq_left.mpr h𝔟.isSubideal]; exact h𝔟
    refine ⟨Quotient.dividedPowers δ hinf, Quotient.isDPMorphism δ hinf, ?_⟩
    intro C _ J'' δ'' g hg
    refine ⟨?_, fun {n} y hy ↦ ?_⟩
    · rw [Ideal.map_map]; exact hg.1
    · obtain ⟨a, ha, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
      rw [Quotient.dpow_apply δ hinf ha]
      exact hg.2 a ha
  · have hset : {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ x ∈ s, y = δ.dpow n x} =
        {y : B | ∃ (n : ℕ) (_ : n ≠ 0) (x : B) (_ : x ∈ s), y = δ.dpow n x} := by
      ext y; simp only [Set.mem_setOf_eq, exists_prop]
    rw [hset, ← SubDPIdeal.span_carrier_eq_dpow_span δ hs]
    exact (SubDPIdeal.span δ s).toIsSubDPIdeal

end GlobalTheory.DPQuot
