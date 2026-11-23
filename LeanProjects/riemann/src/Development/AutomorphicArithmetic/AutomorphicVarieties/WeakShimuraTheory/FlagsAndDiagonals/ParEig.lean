import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem two_by_two {R : Type} [CommRing R] [IsLocalRing R] {a b c e x y : R} (ha : IsUnit a) (he : IsUnit e)
    (hb : b ∈ maximalIdeal R) (h1 : a * x + b * y = 0) (h2 : c * x + e * y = 0) : x = 0 ∧ y = 0 := by
  obtain ⟨u, rfl⟩ := ha
  have hu : (↑u⁻¹ : R) * ↑u = 1 := Units.inv_mul u
  have hx : x = -(↑u⁻¹ * b * y) := by linear_combination (↑u⁻¹ : R) * h1 - x * hu
  have hy' : (e - c * ↑u⁻¹ * b) * y = 0 := by
    rw [hx] at h2
    linear_combination h2
  have hm : c * ↑u⁻¹ * b ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hb
  have hunit : IsUnit (e - c * ↑u⁻¹ * b) := by
    by_contra hn
    have h3 : e - c * ↑u⁻¹ * b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hn
    have h4 : e ∈ maximalIdeal R := by
      have := Ideal.add_mem _ h3 hm
      simpa using this
    exact ((IsLocalRing.mem_maximalIdeal _).1 h4) he
  have hy : y = 0 := hunit.mul_right_eq_zero.1 hy'
  refine ⟨?_, hy⟩
  rw [hx, hy]
  ring

private theorem mem_maxIdeal_of_mul_unit_mem {R : Type} [CommRing R] [IsLocalRing R] {z u : R} (hu : IsUnit u)
    (h : z * u ∈ maximalIdeal R) : z ∈ maximalIdeal R := by
  obtain ⟨w, rfl⟩ := hu
  have := Ideal.mul_mem_right (↑w⁻¹ : R) _ h
  simpa [mul_assoc] using this

theorem UpperTheory.V.Ws.Lab.parEig :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X v : M4 R) (d : Fin 4 → R), (∀ i j, i ≠ j → X i j ∈ maximalIdeal R) →
      (∀ i j, i ≠ j → IsUnit (X i i - X j j)) → Cg (maximalIdeal R) v 1 → X * v = v * Matrix.diagonal d → Par X → Par v := by
  intro R _ _ X v d hoff hdiag hv hXv hX
  have hunit : ∀ i, IsUnit (v i i) := fun i => unit_of_sub_mem isUnit_one (by simpa using hv i i)
  have hE : ∀ i j, ∑ k, X i k * v k j = v i j * d j := fun i j => by
    have := congrFun (congrFun hXv i) j
    rwa [Matrix.mul_apply, Matrix.mul_diagonal] at this
  have hd : ∀ j, X j j - d j ∈ maximalIdeal R := fun j => by
    apply mem_maxIdeal_of_mul_unit_mem (hunit j)
    have e := hE j j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at e
    have hs : (X j j - d j) * v j j = -∑ k ∈ Finset.univ.erase j, X j k * v k j := by
      linear_combination e
    rw [hs, Ideal.neg_mem_iff]
    exact Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _ (hoff j k (Finset.ne_of_mem_erase hk).symm)
  have z01 : X 0 1 = 0 := hX 0 1 (by simp [lamW])
  have z03 : X 0 3 = 0 := hX 0 3 (by simp [lamW])
  have z21 : X 2 1 = 0 := hX 2 1 (by simp [lamW])
  have z23 : X 2 3 = 0 := hX 2 3 (by simp [lamW])
  have key : ∀ j, (0 : Fin 4) ≠ j → (2 : Fin 4) ≠ j → v 0 j = 0 ∧ v 2 j = 0 := by
    intro j h0 h2
    have e0 := hE 0 j
    have e2 := hE 2 j
    rw [Fin.sum_univ_four] at e0 e2
    refine two_by_two (a := X 0 0 - d j) (b := X 0 2) (c := X 2 0) (e := X 2 2 - d j) ?_ ?_
      (hoff 0 2 (by decide)) ?_ ?_
    · refine unit_of_sub_mem (hdiag 0 j h0) ?_
      have : X 0 0 - d j - (X 0 0 - X j j) = X j j - d j := by ring
      rw [this]
      exact hd j
    · refine unit_of_sub_mem (hdiag 2 j h2) ?_
      have : X 2 2 - d j - (X 2 2 - X j j) = X j j - d j := by ring
      rw [this]
      exact hd j
    · linear_combination e0 - v 1 j * z01 - v 3 j * z03
    · linear_combination e2 - v 1 j * z21 - v 3 j * z23
  intro i j hij
  fin_cases i <;> fin_cases j <;> (try simp [lamW] at hij)
  all_goals first
    | exact (key 1 (by decide) (by decide)).1
    | exact (key 1 (by decide) (by decide)).2
    | exact (key 3 (by decide) (by decide)).1
    | exact (key 3 (by decide) (by decide)).2
