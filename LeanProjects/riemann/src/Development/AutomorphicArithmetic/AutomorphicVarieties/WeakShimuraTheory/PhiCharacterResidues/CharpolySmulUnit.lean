import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem charpoly_smul_unit {R n : Type} [CommRing R] [Nontrivial R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (c : R) (hc : IsUnit c) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  have hinj : ∀ p q : R[X], p.comp (C c * X) = q.comp (C c * X) → p = q := by
    intro p q h
    ext i
    have hi := congrArg (fun r => r.coeff i) h
    simp only [comp_C_mul_X_coeff] at hi
    exact (hc.pow i).mul_right_cancel hi
  have key : (Polynomial.eval₂RingHom C (C c * X)).mapMatrix (Matrix.charmatrix (c • M)) =
      C c • Matrix.charmatrix M := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.charmatrix_apply_eq, Matrix.smul_apply, C_mul, mul_sub]
    · simp [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, C_mul]
  have hL : (c • M).charpoly.comp (C c * X) = C c ^ Fintype.card n * M.charpoly := by
    calc (c • M).charpoly.comp (C c * X)
        = Polynomial.eval₂RingHom C (C c * X) (Matrix.charmatrix (c • M)).det := rfl
      _ = (C c • Matrix.charmatrix M).det := by rw [RingHom.map_det, key]
      _ = C c ^ Fintype.card n * M.charpoly := by rw [Matrix.det_smul]; rfl
  have hR : (M.charpoly.scaleRoots c).comp (C c * X) = C c ^ Fintype.card n * M.charpoly := by
    ext i
    rw [comp_C_mul_X_coeff, coeff_scaleRoots, ← C_pow, coeff_C_mul, Matrix.charpoly_natDegree_eq_dim]
    by_cases hi : i ≤ Fintype.card n
    · rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi, mul_comm]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim]; omega)]
      simp
  apply hinj
  rw [hL, hR]

theorem UpperTheory.V.Ws.phiCpMap :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, (X.cp (resLe T.F_le g)).Monic ∧ (X.cp (resLe T.F_le g)).natDegree = 4 ∧ (K.cpT X n g).Monic ∧ (K.cpT X n g).map (algebraMap X.B X.A) = (K.rho X n g).charpoly := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  have hinj : Function.Injective (algebraMap X.B X.A) := X.inj
  haveI : Nontrivial X.A := hinj.nontrivial
  have hmap := X.cp_map (resLe T.F_le g)
  have hmon : (X.cp (resLe T.F_le g)).Monic :=
    monic_of_injective hinj (by rw [hmap]; exact Matrix.charpoly_monic _)
  have hdeg : (X.cp (resLe T.F_le g)).natDegree = 4 := by
    rw [← natDegree_map_eq_of_injective hinj, hmap, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  have hmonT : (K.cpT X n g).Monic := by
    show ((X.cp (resLe T.F_le g)).scaleRoots _).leadingCoeff = 1
    rw [leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]
    exact hmon
  refine ⟨hmon, hdeg, hmonT, ?_⟩
  have hu : IsUnit (K.sc n g) := by
    simp only [UpperTheory.V.Ws.Link.sc]
    exact (Units.isUnit _).mul ((Units.isUnit _).pow n)
  show ((X.cp (resLe T.F_le g)).scaleRoots _).map (algebraMap X.B X.A) = _
  rw [map_scaleRoots _ _ _ (by rw [hmon.leadingCoeff, map_one]; exact one_ne_zero), hmap,
    UpperTheory.V.Ws.Link.rho_apply, charpoly_smul_unit _ _ (hu.map _), ← IsScalarTower.algebraMap_apply]
