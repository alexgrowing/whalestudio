import Mathlib

namespace GlobalTheory

theorem exists_sum_distinct_chars_of_mem_span_char_mul_pow
    (G : Type) [Monoid G] (L : G → ℂ) (f : G → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range fun p : (G →* ℂˣ) × ℕ =>
      fun s : G => ((p.1 s : ℂˣ) : ℂ) * L s ^ p.2)) :
    ∃ (N K : ℕ) (χ : Fin N → G →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ),
      Function.Injective χ ∧
        ∀ t, f t = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * L t ^ (k : ℕ) := by
  classical
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
  set T : Finset (G →* ℂˣ) := a.support.image Prod.fst with hT
  set K : ℕ := a.support.sup Prod.snd with hK
  refine ⟨T.card, K, fun i => (T.equivFin.symm i : G →* ℂˣ),
    fun i k => a ((T.equivFin.symm i : G →* ℂˣ), (k : ℕ)),
    Subtype.val_injective.comp T.equivFin.symm.injective, fun t => ?_⟩
  let g : (G →* ℂˣ) × ℕ → ℂ := fun p => a p * ((p.1 t : ℂˣ) : ℂ) * L t ^ p.2
  have h1 : f t = ∑ p ∈ a.support, g p := by
    rw [← ha, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [g, mul_assoc]
  have h2 : ∑ p ∈ a.support, g p = ∑ p ∈ T ×ˢ Finset.range (K + 1), g p := by
    refine Finset.sum_subset (fun p hp => ?_) (fun p _ hp => ?_)
    · refine Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, ?_⟩
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := Prod.snd) hp))
    · simp [g, Finsupp.notMem_support_iff.mp hp]
  rw [h1, h2, Finset.sum_product, ← Finset.sum_coe_sort T,
    ← Equiv.sum_comp T.equivFin.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range]

end GlobalTheory
