import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private def formJ (R : Type) [CommRing R] : M4 R := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

private theorem formJ_mul (R : Type) [CommRing R] : (formJ R).transpose * formJ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formJ, Matrix.mul_apply, Fin.sum_univ_four]

private theorem adj_eq_conj {R : Type} [CommRing R] (M : M4 R) :
    adj M = formJ R * (M.transpose * (formJ R).transpose) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formJ, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four]

theorem UpperTheory.V.Ws.phiAdj :
    ∀ {R : Type} [CommRing R] (ν : R) (M N : M4 R), IsGSp ν M → M * N = 1 → (ν • N).charpoly = M.charpoly := by
  intro R _ ν M N hM hMN
  have h1 : adj M = ν • N := by
    have h2 : adj M * M * N = ν • N := by
      unfold IsGSp at hM
      rw [hM, smul_mul_assoc, one_mul]
    rw [mul_assoc, hMN, mul_one] at h2
    exact h2
  rw [← h1, adj_eq_conj, Matrix.charpoly_mul_comm, mul_assoc, formJ_mul, mul_one, Matrix.charpoly_transpose]
