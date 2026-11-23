import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.minorDeg :
    ∀ (n : ℕ) (k : Fin n), minor k ≠ 0 ∧ (minor k).totalDegree ≤ (k : ℕ) + 1 := by
  intro n k
  constructor
  · intro h
    have h0 := congrArg
      (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℂ) else 0)) h
    rw [minor, RingHom.map_det, map_zero] at h0
    rw [show (RingHom.mapMatrix _) _ = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) from ?_] at h0
    · simp at h0
    · ext i j
      simp [Matrix.one_apply, Fin.castLE_inj]
  · rw [minor, Matrix.det_apply]
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
    refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
    simp [MvPolynomial.totalDegree_X]
