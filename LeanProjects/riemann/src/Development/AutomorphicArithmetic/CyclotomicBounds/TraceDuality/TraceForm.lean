import Mathlib
open NumberField
open scoped TensorProduct NNReal

theorem UpperTheory.WildB.traceForm :
    ∀ (E : Type) [Field E] [NumberField E] (d : 𝓞 E) (m : ℕ), d ≠ 0 → (∀ a ∈ differentIdeal ℤ (𝓞 E), d ∣ (m : 𝓞 E) * a) → ∃ lam : 𝓞 E →+ ℤ, ∀ x : 𝓞 E, (lam x : ℚ) = Algebra.trace ℚ E ((m : E) * (x : E) / (d : E)) := by
  intro E _ _ d m hd h
  classical
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd
  have hne : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ (by simp)
  have hmem : (m : E) / (d : E) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)),
      FractionalIdeal.mem_inv_iff (inv_ne_zero hne), ← coeIdeal_differentIdeal ℤ ℚ]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    obtain ⟨c, hc⟩ := h a ha
    refine (FractionalIdeal.mem_one_iff _).2 ⟨c, ?_⟩
    have h2 := congrArg (algebraMap (𝓞 E) E) hc
    rw [map_mul, map_mul, map_natCast] at h2
    change (m : E) * (a : E) = (d : E) * (c : E) at h2
    change (c : E) = (m : E) / (d : E) * (a : E)
    rw [div_mul_eq_mul_div, h2, mul_div_cancel_left₀ _ hd']
  rw [FractionalIdeal.mem_dual (by simp)] at hmem
  have hx : ∀ x : 𝓞 E, ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ E ((m : E) * (x : E) / (d : E)) := by
    intro x
    obtain ⟨n, hn⟩ := hmem (x : E) ((FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply, div_mul_eq_mul_div] at hn
    exact hn
  choose f hf using hx
  refine ⟨AddMonoidHom.mk' f (fun x y => ?_), fun x => hf x⟩
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_add, hf, hf, hf, ← map_add]
  congr 1
  push_cast
  ring
