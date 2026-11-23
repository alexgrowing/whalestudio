import Mathlib

private theorem UpperTheory.Reformulated.B.LayerApproximation.first_layer {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] (m : Ideal R) (A : Subalgebra O R) (T : Set R)
    (h0 : ∀ (x : R), ∃ (a : O), x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ (2 : ℕ)) :
    ∀ x ∈ m, ∃ a ∈ A, a ∈ m ∧ x - a ∈ m ^ 2 := by
  have hspan : ∀ y ∈ Ideal.span T, ∃ a ∈ A, a ∈ m ∧ y - a ∈ m ^ 2 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht => exact ⟨t, (hT t ht).1, (hT t ht).2, by simp⟩
    | zero => exact ⟨0, A.zero_mem, m.zero_mem, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, ham, hua⟩ := hu
      obtain ⟨b, hb, hbm, hvb⟩ := hv
      refine ⟨a + b, A.add_mem ha hb, m.add_mem ham hbm, ?_⟩
      have e : u + v - (a + b) = (u - a) + (v - b) := by ring
      rw [e]
      exact Ideal.add_mem _ hua hvb
    | smul r u _ hu =>
      obtain ⟨a, ha, ham, hua⟩ := hu
      obtain ⟨c, hc⟩ := h0 r
      refine ⟨algebraMap O R c * a, A.mul_mem (A.algebraMap_mem c) ha,
        m.mul_mem_left _ ham, ?_⟩
      have e : r • u - algebraMap O R c * a = r * (u - a) + (r - algebraMap O R c) * a := by
        rw [smul_eq_mul]; ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hua) ?_
      rw [pow_two]
      exact Ideal.mul_mem_mul hc ham
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hm hx)
  obtain ⟨a, ha, ham, hya⟩ := hspan y hy
  refine ⟨a, ha, ham, ?_⟩
  have e : y + z - a = (y - a) + z := by ring
  rw [e]
  exact Ideal.add_mem _ hya hz

private theorem UpperTheory.Reformulated.B.LayerApproximation.all_layers {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] (m : Ideal R) (A : Subalgebra O R)
    (h0 : ∀ (x : R), ∃ (a : O), x - algebraMap O R a ∈ m)
    (h1 : ∀ x ∈ m, ∃ a ∈ A, a ∈ m ∧ x - a ∈ m ^ 2) (N : ℕ) :
    ∀ x ∈ m ^ N, ∃ a ∈ A, a ∈ m ^ N ∧ x - a ∈ m ^ (N + 1) := by
  induction N with
  | zero =>
    intro x _
    obtain ⟨c, hc⟩ := h0 x
    exact ⟨algebraMap O R c, A.algebraMap_mem c, by simp, by simpa using hc⟩
  | succ N ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      obtain ⟨a, ha, ham, hya⟩ := ih y hy
      obtain ⟨b, hb, hbm, hzb⟩ := h1 z hz
      refine ⟨a * b, A.mul_mem ha hb, ?_, ?_⟩
      · rw [pow_succ]
        exact Ideal.mul_mem_mul ham hbm
      · have e : y * z - a * b = y * (z - b) + (y - a) * b := by ring
        rw [e]
        refine Ideal.add_mem _ ?_ ?_
        · rw [show N + 1 + 1 = N + 2 from rfl, pow_add]
          exact Ideal.mul_mem_mul hy hzb
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hya hbm
    · rintro u v ⟨a, ha, ham, hua⟩ ⟨b, hb, hbm, hvb⟩
      refine ⟨a + b, A.add_mem ha hb, Ideal.add_mem _ ham hbm, ?_⟩
      have e : u + v - (a + b) = (u - a) + (v - b) := by ring
      rw [e]
      exact Ideal.add_mem _ hua hvb

theorem UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx :
    ∀ {O R : Type} [inst : CommRing O] [inst_1 : CommRing R]
    [inst_2 : Algebra O R] (m : Ideal R) (A : Subalgebra O R) (T : Set R),
    (∀ (x : R), ∃ (a : O), x - (Algebra.algebraMap O R : O → R) a ∈ m) →
      (∀ t ∈ T, t ∈ A ∧ t ∈ m) → m ≤ Ideal.span T ⊔ m ^ (2 : ℕ) → ∀ (N : ℕ) (x : R), ∃ a ∈ A, x - a ∈ m ^ N := by
  intro O R _ _ _ m A T h0 hT hm N x
  have h1 := UpperTheory.Reformulated.B.LayerApproximation.first_layer m A T h0 hT hm
  induction N with
  | zero => exact ⟨0, A.zero_mem, by simp⟩
  | succ N ih =>
    obtain ⟨a, ha, hxa⟩ := ih
    obtain ⟨b, hb, -, hab⟩ := UpperTheory.Reformulated.B.LayerApproximation.all_layers m A h0 h1 N _ hxa
    refine ⟨a + b, A.add_mem ha hb, ?_⟩
    have e : x - (a + b) = x - a - b := by ring
    rw [e]
    exact hab
