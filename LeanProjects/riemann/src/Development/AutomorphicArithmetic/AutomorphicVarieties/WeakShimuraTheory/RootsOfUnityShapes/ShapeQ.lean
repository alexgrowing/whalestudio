import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rq.shapeQ :
    ∀ (R : Type) [CommRing R] (X n₀ : M4 R), SuppM nP X → (∀ i, IsUnit (X i i)) → IsLow n₀ → SuppM qQ n₀ →
      (IsUnit ((X * n₀) 0 0) ∧ IsUnit ((X * n₀) 0 0 * (X * n₀) 1 1 - (X * n₀) 0 1 * (X * n₀) 1 0)) ∧
        ∀ n : M4 R, IsLow n → IsUp (adj n * X * n₀) → SuppM qQ n := by
  intro R _ X n₀ hX hu h0 hq
  obtain ⟨-, hd, hl⟩ := h0
  have x01 : X 0 1 = 0 := hX 0 1 (by decide) (by decide)
  have x02 : X 0 2 = 0 := hX 0 2 (by decide) (by decide)
  have x03 : X 0 3 = 0 := hX 0 3 (by decide) (by decide)
  have x13 : X 1 3 = 0 := hX 1 3 (by decide) (by decide)
  have x23 : X 2 3 = 0 := hX 2 3 (by decide) (by decide)
  have x21 : X 2 1 = 0 := hX 2 1 (by decide) (by decide)
  have n21 : n₀ 2 1 = 0 := hq 2 1 (by decide) (by decide)
  have n01 : n₀ 0 1 = 0 := hl 0 1 (by decide)
  have y00 : (X * n₀) 0 0 = X 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, x01, x02, x03, hd]
  have y01 : (X * n₀) 0 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, x01, x02, x03, n01]
  have y11 : (X * n₀) 1 1 = X 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, x13, n21, n01, hd]
  have y21 : (X * n₀) 2 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, x21, x23, n21, n01]
  refine ⟨⟨y00 ▸ hu 0, ?_⟩, fun n hn hU => ?_⟩
  · rw [y00, y11, y01, zero_mul, sub_zero]
    exact (hu 0).mul (hu 1)
  · obtain ⟨hg, nd, nl⟩ := hn
    have h1 : adj n * n = 1 := by
      have := hg
      unfold IsGSp at this
      rwa [one_smul] at this
    have h2 : n * adj n = 1 := mul_eq_one_comm.mp h1
    set U := adj n * X * n₀ with hUdef
    have hY : X * n₀ = n * U := by
      rw [hUdef, mul_assoc (adj n), ← mul_assoc n, h2, one_mul]
    have u21 : U 2 1 = 0 := hU 2 1 (by decide)
    have u31 : U 3 1 = 0 := hU 3 1 (by decide)
    have m01 : n 0 1 = 0 := nl 0 1 (by decide)
    have u01 : U 0 1 = 0 := by
      rw [hY] at y01
      simpa [Matrix.mul_apply (M := n), Fin.sum_univ_four, u21, u31, m01, nd] using y01
    have u11 : U 1 1 = X 1 1 := by
      rw [hY] at y11
      simpa [Matrix.mul_apply (M := n), Fin.sum_univ_four, u21, u31, u01, nd] using y11
    have m21 : n 2 1 = 0 := by
      rw [hY, Matrix.mul_apply, Fin.sum_univ_four, u01, u21, u31, u11, mul_zero, mul_zero, mul_zero,
        zero_add, add_zero, add_zero] at y21
      exact (hu 1).mul_left_eq_zero.mp y21
    intro i j hij hw
    have key : i < j ∨ (i = 2 ∧ j = 1) := by
      revert i j
      decide
    rcases key with h | ⟨rfl, rfl⟩
    · exact nl i j h
    · exact m21
