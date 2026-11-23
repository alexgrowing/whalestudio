import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.X1.exists_symplectic_diagonalizing_lift {A R : Type} [CommRing A] [CommRing R] (f : A →+* R)
    (hsq : ∀ a b, f a = 0 → f b = 0 → a * b = 0) (ν : A) (X : M4 A) (hν : IsUnit ν) (hX : IsGSp ν X)
    (hd : ∀ i j, i ≠ j → f (X i j) = 0) (hu : ∀ i j, i ≠ j → IsUnit (X i i - X j j)) :
    ∃ u : M4 A, IsGSp 1 u ∧ u.map f = 1 ∧ (adj u * X * u).IsDiag := by
  obtain ⟨hmul, -, hadd, -, hone, hmap, -⟩ := grp A
  have mz : ∀ M M' : M4 A, M.map f = 0 → M'.map f = 0 → M * M' = 0 := by
    intro M M' h h'
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => hsq _ _ (congrFun (congrFun h i) k) (congrFun (congrFun h' k) j)
  set D : M4 A := Matrix.diagonal fun i => X i i with hD
  set E : M4 A := X - D with hE
  have hXE : X = D + E := by rw [hE]; abel
  have Eii : ∀ i, E i i = 0 := fun i => by simp [hE, hD]
  have Eij : ∀ i j, i ≠ j → E i j = X i j := fun i j h => by simp [hE, hD, Matrix.diagonal_apply_ne _ h]
  have Ef : E.map f = 0 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Eii]
    · simp [Eij i j h, hd i j h]
  have aEf : (adj E).map f = 0 := by
    rw [← hmap, Ef]; ext i j; simp [adj_apply]
  have aD : adj D = Matrix.diagonal fun i => X i.rev i.rev := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, hD, Matrix.diagonal_apply]
  have key : adj D * D + (adj D * E + adj E * D) = ν • (1 : M4 A) := by
    have h : adj (D + E) * (D + E) = ν • (1 : M4 A) := by rw [← hXE]; exact hX
    rw [hadd, add_mul, mul_add, mul_add, mz _ _ aEf Ef] at h
    rw [← h]; abel
  have k1 : ∀ i, X i.rev i.rev * X i i = ν := fun i => by
    have h := congrFun (congrFun key i) i
    rw [aD, hD] at h
    simpa [Matrix.diagonal_mul_diagonal, adj_apply, Eii] using h
  have k2 : ∀ i j, i ≠ j → X i.rev i.rev * E i j + adj E i j * X j j = 0 := fun i j hij => by
    have h := congrFun (congrFun key i) j
    rw [aD, hD] at h
    simpa [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij] using h
  set N : M4 A := Matrix.of fun i j => -(E i j * Ring.inverse (X i i - X j j)) with hN
  have Nf : N.map f = 0 := by
    ext i j
    have h : f (E i j) = 0 := congrFun (congrFun Ef i) j
    simp [hN, h]
  have N1 : ∀ i j, i ≠ j → N i j * (X i i - X j j) = -E i j := fun i j h => by
    rw [hN, Matrix.of_apply, neg_mul, mul_assoc, Ring.inverse_mul_cancel _ (hu i j h), mul_one]
  have aN : adj N = -N := by
    ext i j
    by_cases h : i = j
    · subst h; simp [adj_apply, hN, Eii]
    · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
      have uj : IsUnit (X j j) := isUnit_of_mul_isUnit_right (by rw [k1 j]; exact hν)
      have e1 := N1 i j h
      have e2 : adj N i j * (X j.rev j.rev - X i.rev i.rev) = -adj E i j := by
        rw [adj_apply, adj_apply, smul_mul_assoc, N1 _ _ h', smul_neg]
      refine ((hu _ _ h').mul uj).mul_left_inj.mp ?_
      rw [Matrix.neg_apply]
      linear_combination X j j * e2 - k2 i j h + X i.rev i.rev * e1 + N i j * k1 j - N i j * k1 i
  have au : adj (1 + N) = 1 - N := by rw [hadd, hone, aN, sub_eq_add_neg]
  refine ⟨1 + N, ?_, ?_, ?_⟩
  · unfold IsGSp
    rw [au, one_smul, sub_mul, mul_add N, mz _ _ Nf Nf]
    simp
  · rw [Matrix.map_add _ (map_add f), Nf, add_zero, Matrix.map_one _ (map_zero f) (map_one f)]
  · have NDf : (N * D).map f = 0 := by rw [Matrix.map_mul, Nf, zero_mul]
    have e : adj (1 + N) * X * (1 + N) = D + (E + D * N - N * D) := by
      have : (1 - N) * (D + E) * (1 + N) = D + (E + D * N - N * D) + (E * N - N * D * N - N * E - N * E * N) := by
        noncomm_ring
      rw [au]
      conv_lhs => rw [hXE]
      rw [this, mz _ _ Ef Nf, mz _ _ NDf Nf, mz _ _ Nf Ef]
      simp
    intro i j h
    rw [e, hD]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.diagonal_apply_ne _ h]
    linear_combination N1 i j h

theorem UpperTheory.V.Ws.X1.diagLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : A) (X : M4 A), IsUnit ν → IsGSp ν X → (X.map p).IsDiag → (∀ i j, i ≠ j → IsUnit (X i i - X j j)) → ∃ u : M4 A, IsGSp 1 u ∧ u.map p = 1 ∧ (adj u * X * u).IsDiag := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p _ hk ν X hν hX hd hu
  have hle : RingHom.ker p ≤ maximalIdeal A := le_maximalIdeal (RingHom.ker_ne_top p)
  refine UpperTheory.V.Ws.X1.exists_symplectic_diagonalizing_lift (p : A →+* R) (fun a b ha hb => ?_) ν X hν hX (fun i j h => hd h) hu
  have h : a * b ∈ maximalIdeal A * RingHom.ker p := Ideal.mul_mem_mul (hle ha) hb
  rwa [hk] at h
