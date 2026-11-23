import Mathlib

namespace GlobalTheory.FactorThroughProjection

theorem exists_factor_through_projection {J : Type} [Fintype J] [DecidableEq J] (A : J → Type)
    [inst : (i : J) → CommRing (A i)] {k : Type} [inst_1 : CommRing k] [IsDomain k]
    (χ : ((i : J) → A i) →+* k) :
    ∃ (i : J) (ψ : A i →+* k), ∀ (x : (i : J) → A i), χ x = ψ (x i) := by
  have hsum : ∑ i : J, χ (Pi.single i (1 : A i)) = 1 := by
    rw [← map_sum]
    have h : ∑ i : J, (Pi.single i (1 : A i) : (j : J) → A j) = 1 :=
      Finset.univ_sum_single (1 : (j : J) → A j)
    rw [h, map_one]
  have hne : ∑ i : J, χ (Pi.single i (1 : A i)) ≠ 0 := by
    rw [hsum]; exact one_ne_zero
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hmul : ∀ a b : A i, (Pi.single i (a * b) : (j : J) → A j)
      = Pi.single i a * Pi.single i b := by
    intro a b
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  have hone : χ (Pi.single i (1 : A i)) = 1 := by
    apply mul_left_cancel₀ hi
    rw [← map_mul, ← hmul, mul_one, mul_one]
  let ψ : A i →+* k :=
    { toFun := fun a => χ (Pi.single i a)
      map_one' := hone
      map_mul' := fun a b => by rw [hmul, map_mul]
      map_zero' := by simp
      map_add' := fun a b => by rw [Pi.single_add, map_add] }
  refine ⟨i, ψ, fun x => ?_⟩
  change χ x = χ (Pi.single i (x i))
  have hx : (Pi.single i (x i) : (j : J) → A j) = x * Pi.single i (1 : A i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [hx, map_mul, hone, mul_one]

end GlobalTheory.FactorThroughProjection
