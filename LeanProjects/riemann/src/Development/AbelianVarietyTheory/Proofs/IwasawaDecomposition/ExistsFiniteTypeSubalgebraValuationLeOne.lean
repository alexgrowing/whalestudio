import Mathlib

namespace GlobalTheory.FractionalParts

def fracs {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (C : Subalgebra A B) :
    Subalgebra A B where
  carrier := {b | ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a}
  mul_mem' := by
    rintro x y ⟨a, ha, s, hs, hu, h⟩ ⟨a', ha', s', hs', hu', h'⟩
    exact ⟨a * a', C.mul_mem ha ha', s * s', C.mul_mem hs hs', hu.mul hu', by
      rw [← h, ← h']; ring⟩
  add_mem' := by
    rintro x y ⟨a, ha, s, hs, hu, h⟩ ⟨a', ha', s', hs', hu', h'⟩
    exact ⟨s' * a + s * a', C.add_mem (C.mul_mem hs' ha) (C.mul_mem hs ha'), s * s',
      C.mul_mem hs hs', hu.mul hu', by rw [← h, ← h']; ring⟩
  algebraMap_mem' r := ⟨algebraMap A B r, C.algebraMap_mem r, 1, C.one_mem, isUnit_one, one_mul _⟩

theorem exists_finiteType_subalgebra_valuation_le_one (A B k : Type) [CommRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k)
    (V : ValuationSubring k) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal B)
    (hA : ∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) :
    ∃ C : Subalgebra A B, Algebra.FiniteType A C ∧ (∀ c ∈ C, V.valuation (φ c) ≤ 1) ∧
      ∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a := by
  classical
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff A B).mp inferInstance
  have key : ∀ x : B, ∃ y : B, φ y ∈ V ∧ (y = x ∨ y * x = 1) := by
    intro x
    by_cases hx : φ x ∈ V
    · exact ⟨x, hx, Or.inl rfl⟩
    · have hne : φ x ≠ 0 := fun h => hx (h ▸ V.zero_mem)
      have hu : IsUnit x := by
        by_contra hnu
        have : x ∈ RingHom.ker φ := by
          rw [hker]; exact (IsLocalRing.mem_maximalIdeal x).mpr hnu
        exact hne this
      obtain ⟨y, hy⟩ := hu.exists_left_inv
      refine ⟨y, ?_, Or.inr hy⟩
      have h1 : φ y * φ x = 1 := by rw [← map_mul, hy, map_one]
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (V.mem_or_inv_mem (φ x)).resolve_left hx
  choose f hfV hf using key
  let C : Subalgebra A B := Algebra.adjoin A ((σ.image f : Finset B) : Set B)
  have hfC : ∀ x ∈ σ, f x ∈ C := fun x hx =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem f hx))
  refine ⟨C, ?_, ?_, ?_⟩
  · exact (Subalgebra.fg_iff_finiteType C).mp (Subalgebra.fg_adjoin_finset _)
  · intro c hc
    rw [ValuationSubring.valuation_le_one_iff]
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact hfV z
    | algebraMap r => exact (V.valuation_le_one_iff _).mp (hA r)
    | add x y _ _ hx hy => rw [map_add]; exact V.add_mem _ _ hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact V.mul_mem _ _ hx hy
  · have hle : Algebra.adjoin A (σ : Set B) ≤ fracs C := by
      refine Algebra.adjoin_le ?_
      intro x hx
      have hx' := hfC x (Finset.mem_coe.mp hx)
      rcases hf x with h | h
      · exact ⟨x, h ▸ hx', 1, C.one_mem, isUnit_one, one_mul _⟩
      · exact ⟨1, C.one_mem, f x, hx', IsUnit.of_mul_eq_one _ h, h⟩
    intro b
    obtain ⟨t, ht, htu, hbt⟩ := hσ b
    obtain ⟨a1, ha1, s1, hs1, hu1, h1⟩ := hle ht
    obtain ⟨a2, ha2, s2, hs2, hu2, h2⟩ := hle hbt
    refine ⟨s1 * a2, C.mul_mem hs1 ha2, s2 * a1, C.mul_mem hs2 ha1,
      hu2.mul (h1 ▸ hu1.mul htu), ?_⟩
    rw [← h1, ← h2]; ring

end GlobalTheory.FractionalParts
