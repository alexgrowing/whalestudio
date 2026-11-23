import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem de_eq_det (R : Type) [CommRing R] (n : ℕ) :
    De R n = (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).det := by
  rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j
  simp

private theorem nn_ne (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) : NN n q ≠ 0 := by
  rw [NN, Finset.prod_ne_zero_iff]
  intro p hp
  have hlt : p.1 < p.2 := by simpa [pairs] using hp
  intro h
  have hc := congrArg (coeff (Finsupp.single p.2 1)) h
  rw [coeff_sub, coeff_C_mul, coeff_X, coeff_X', coeff_zero] at hc
  simp [Finsupp.single_left_inj one_ne_zero, hlt.ne] at hc

theorem UpperTheory.V.AlgebraTools.hkDe :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), De R n ≠ 0 ∧ (∀ w : Perm (Fin n), rename w (De R n) = Perm.sign w • De R n) ∧ ∀ q : R, NN n q ≠ 0 := by
  intro R _ _ n
  refine ⟨?_, ?_, nn_ne R n⟩
  · rw [de_eq_det, Matrix.det_vandermonde_ne_zero_iff]
    exact X_injective
  · intro w
    rw [de_eq_det, AlgHom.map_det]
    have hm : (rename w : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).mapMatrix
        (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)) =
        (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).submatrix w id := by
      ext i j
      simp [Matrix.vandermonde_apply]
    rw [hm, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
