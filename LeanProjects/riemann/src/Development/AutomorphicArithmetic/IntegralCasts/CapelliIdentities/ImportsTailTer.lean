import Mathlib

theorem UpperTheory.Reformulated.B.Yra3.main :
    ∀ {R L : Type} [inst : CommRing R] [inst_1 : CommRing L] (φ : R →+* L),
      (∀ (z : L), ∃ (a : R) (b : R), IsUnit ((φ : R → L) b) ∧ z * (φ : R → L) b = (φ : R → L) a) →
        ∀ (s : Finset L), ∃ (b : R), IsUnit ((φ : R → L) b) ∧ ∀ z ∈ s, z * (φ : R → L) b ∈ Set.range (⇑φ : R → L) := by
  intro R L _ _ φ h s
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert z s _ ih =>
    obtain ⟨b0, hb0, hs⟩ := ih
    obtain ⟨a, b, hb, hz⟩ := h z
    refine ⟨b0 * b, by rw [map_mul]; exact hb0.mul hb, ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · refine ⟨a * b0, ?_⟩
      rw [map_mul, map_mul, ← hz]; ring
    · obtain ⟨c, hc⟩ := hs w hw
      refine ⟨c * b, ?_⟩
      rw [map_mul, map_mul, hc]; ring
