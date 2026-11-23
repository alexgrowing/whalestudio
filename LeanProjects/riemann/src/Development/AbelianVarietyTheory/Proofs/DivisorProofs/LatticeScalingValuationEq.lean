import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem scalar_of_lattice_image : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V W : Type) [AddCommGroup V] [Module C V] [AddCommGroup W] [Module C W] (LV : Set V) (LW : Set W) (δ : V ≃ₗ[C] C) (δ' : W ≃ₗ[C] C) (ι : V →ₗ[C] W) (lam : C), v.Integers O → (∀ w, w ∈ LV ↔ δ w ∈ (algebraMap O C).range) → (∀ w, w ∈ LW ↔ δ' w ∈ (algebraMap O C).range) → ι '' LV = (fun w => lam • w) '' LW → ∃ l₀ : C, v l₀ = v lam ∧ ∀ w, δ' (ι w) = l₀ * δ w := by
  intro C _ v O _ _ V W _ _ _ _ LV LW δ δ' ι lam hO hV hW himg
  have hdec : ∀ u : V, u = (δ u) • δ.symm 1 := by
    intro u; apply δ.injective; simp
  refine ⟨δ' (ι (δ.symm 1)), ?_, ?_⟩
  · have h1 : δ.symm 1 ∈ LV := by
      rw [hV]; exact ⟨1, by simp⟩
    have h2 : ι (δ.symm 1) ∈ (fun w => lam • w) '' LW := himg ▸ Set.mem_image_of_mem ι h1
    obtain ⟨w', hw', hw'eq⟩ := h2
    rw [hW] at hw'
    obtain ⟨o, ho⟩ := hw'
    have e1 : δ' (ι (δ.symm 1)) = lam * algebraMap O C o := by
      rw [← hw'eq]; simp only [map_smul, smul_eq_mul, ho]
    have h3 : δ'.symm 1 ∈ LW := by
      rw [hW]; exact ⟨1, by simp⟩
    have h4 : lam • δ'.symm 1 ∈ ι '' LV := himg ▸ ⟨_, h3, rfl⟩
    obtain ⟨u, hu, hueq⟩ := h4
    rw [hV] at hu
    obtain ⟨o', ho'⟩ := hu
    have e2 : lam = δ' (ι (δ.symm 1)) * algebraMap O C o' := by
      have h5 : δ' (ι u) = lam := by rw [hueq]; simp
      rw [← h5, hdec u, map_smul, map_smul, smul_eq_mul, ← ho']
      ring
    apply le_antisymm
    · rw [e1, map_mul]; exact mul_le_of_le_one_right zero_le' (hO.map_le_one o)
    · rw [e2, map_mul]; exact mul_le_of_le_one_right zero_le' (hO.map_le_one o')
  · intro w
    calc δ' (ι w) = δ' (ι ((δ w) • δ.symm 1)) := by rw [← hdec w]
      _ = δ' (ι (δ.symm 1)) * δ w := by rw [map_smul, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.DetInv
