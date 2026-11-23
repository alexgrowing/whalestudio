import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem degType_pos (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : ∀ d ∈ degType g f, 0 < d := by
  intro d hd
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hd
  exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP).natDegree_pos

theorem degType_sum (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) (hf : f ≠ 0) :
    (degType g f).sum = f.natDegree := by
  unfold degType
  rw [← natDegree_multiset_prod _ (UniqueFactorizationMonoid.zero_notMem_normalizedFactors f)]
  exact natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (UniqueFactorizationMonoid.prod_normalizedFactors hf))

theorem prod_pow_sub_one_le (g : ℕ) (s : Multiset ℕ) :
    (s.map fun d => g ^ d - 1).prod ≤ g ^ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, pow_add]
    exact Nat.mul_le_mul (Nat.sub_le _ _) ih

theorem ne_zero_natDegree_of_mem_sqSet (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X])
    (hf : f ∈ sqSet g N) : f ≠ 0 ∧ f.natDegree = N := by
  unfold sqSet at hf
  rw [Finset.mem_filter, Finset.mem_image] at hf
  obtain ⟨⟨c, -, rfl⟩, -⟩ := hf
  have h : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N := degree_sum_fin_lt c
  refine ⟨(monic_X_pow_add h).ne_zero, ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]

theorem torusCard_bounds_mul : ∀ (g : ℕ) [Fact g.Prime], (∀ (N : ℕ), ∀ f ∈ sqSet g N, 0 < torusCard g f ∧ torusCard g f ≤ g ^ N ∧ (degType g f).sum = N ∧ ∀ d ∈ degType g f, 0 < d) ∧ (∀ h f : (ZMod g)[X], h ≠ 0 → f ≠ 0 → degType g (h * f) = degType g h + degType g f ∧ torusCard g (h * f) = torusCard g h * torusCard g f) ∧ ∀ P : (ZMod g)[X], Irreducible P → degType g P = {P.natDegree} ∧ torusCard g P = g ^ P.natDegree - 1 := by
  intro g hg
  refine ⟨fun N f hf => ?_, fun h f hh hf => ?_, fun P hP => ?_⟩
  · obtain ⟨h0, hN⟩ := ne_zero_natDegree_of_mem_sqSet g N f hf
    have hs : (degType g f).sum = N := (degType_sum g f h0).trans hN
    refine ⟨?_, ?_, hs, degType_pos g f⟩
    · unfold torusCard
      apply Multiset.prod_pos
      intro a ha
      obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.1 ha
      exact Nat.sub_pos_of_lt (Nat.one_lt_pow (degType_pos g f d hd).ne' hg.out.one_lt)
    · rw [← hs]
      exact prod_pow_sub_one_le g _
  · have hd : degType g (h * f) = degType g h + degType g f := by
      unfold degType
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hh hf, Multiset.map_add]
    refine ⟨hd, ?_⟩
    unfold torusCard
    rw [hd, Multiset.map_add, Multiset.prod_add]
  · have hd : degType g P = {P.natDegree} := by
      unfold degType
      rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP, Multiset.map_singleton]
      congr 1
      exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (normalize_associated P))
    refine ⟨hd, ?_⟩
    unfold torusCard
    rw [hd, Multiset.map_singleton, Multiset.prod_singleton]

end GlobalTheory.BadShare
