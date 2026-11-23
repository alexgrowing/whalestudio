import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.Rt.pow_graded {k : Type} [Field k] (h : Fin 4 → ℕ) (N : M4 k)
    (hN : ∀ i j, h j ≤ h i → N i j = 0) (n : ℕ) : ∀ i j, h j < h i + n → (N ^ n) i j = 0 := by
  induction n with
  | zero =>
    intro i j hij
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    omega
  | succ n ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : h m < h i + n
    · rw [ih i m hm, zero_mul]
    · rw [hN m j (by omega), mul_zero]

private theorem UpperTheory.V.Ws.Rt.pow_char_graded {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l]
    (S : Finset (ℤ × ℤ)) (h : Fin 4 → ℕ) (hl : ∀ i, h i < l) (hS : ∀ i j, i ≠ j → h j ≤ h i → wt i j ∉ S)
    (X : M4 k) (h1 : ∀ i, X i i = 1) (hX : SuppM S X) : X ^ l = 1 := by
  obtain ⟨N, hNdef⟩ : ∃ N : M4 k, N = X - 1 := ⟨_, rfl⟩
  have hXN : X = 1 + N := by rw [hNdef]; abel
  have hN : ∀ i j, h j ≤ h i → N i j = 0 := by
    intro i j hij
    rw [hNdef, Matrix.sub_apply]
    by_cases hij' : i = j
    · subst hij'
      rw [h1, Matrix.one_apply_eq, sub_self]
    · rw [hX i j hij' (hS i j hij' hij), Matrix.one_apply_ne hij', sub_self]
  have hNl : N ^ l = 0 := by
    ext i j
    rw [Matrix.zero_apply]
    exact UpperTheory.V.Ws.Rt.pow_graded h N hN l i j (by have := hl j; omega)
  haveI : CharP (Matrix (Fin 4) (Fin 4) k) l := inferInstance
  rw [hXN, add_pow_char_of_commute (p := l) (h := Commute.one_left N), one_pow, hNl, add_zero]

theorem UpperTheory.V.Ws.Rt.unipPow :
    ∀ (k : Type) [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (X : M4 k), (∀ i, X i i = 1) →
      ((5 ≤ l ∧ (SuppM nP X ∨ SuppM nM X)) ∨ (3 ≤ l ∧ SuppM qQ X)) → X ^ l = 1 := by
  intro k _ l _ _ X h1 h
  rcases h with ⟨hl, h | h⟩ | ⟨hl, h⟩
  · refine UpperTheory.V.Ws.Rt.pow_char_graded l nP ![3, 1, 2, 0] (fun i => ?_) (by decide) X h1 h
    fin_cases i <;> simp <;> omega
  · refine UpperTheory.V.Ws.Rt.pow_char_graded l nM ![3, 2, 1, 0] (fun i => ?_) (by decide) X h1 h
    fin_cases i <;> simp <;> omega
  · refine UpperTheory.V.Ws.Rt.pow_char_graded l qQ ![2, 1, 1, 0] (fun i => ?_) (by decide) X h1 h
    fin_cases i <;> simp <;> omega
