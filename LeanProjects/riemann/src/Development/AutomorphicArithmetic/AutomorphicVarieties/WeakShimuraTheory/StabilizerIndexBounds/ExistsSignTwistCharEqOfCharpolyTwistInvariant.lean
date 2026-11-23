import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CharPerm

open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem charpoly_neg_roots_neg {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : Fin n → R)
    (h : M.charpoly = ∏ i, (X - C (a i))) : (-M).charpoly = ∏ i, (X - C (-a i)) := by
  have h1 : (-M).charmatrix = -((compRingHom (-X : R[X])).mapMatrix M.charmatrix) := by
    ext i j : 1
    by_cases e : i = j
    · subst e
      simp [Matrix.charmatrix_apply_eq]
      ring
    · simp [Matrix.charmatrix_apply_ne _ _ _ e]
  have h2 := congrArg (compRingHom (-X : R[X])) h
  rw [Matrix.charpoly, RingHom.map_det, map_prod] at h2
  rw [Matrix.charpoly, h1, Matrix.det_neg, h2]
  have h3 : (-1 : R[X]) ^ Fintype.card (Fin n) = ∏ _i : Fin n, (-1 : R[X]) := by
    rw [Finset.prod_const, Finset.card_univ]
  rw [h3, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp
  ring

theorem UpperTheory.V.Ws.exists_sign_twist_char_eq_of_charpoly_twist_invariant :
    ∀ (K k k' B G : Type) [Field K] [Field k] [Field k'] [CommRing B] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) B)
      (j : B →+* K) (φ : B →+* k') (ι : k →+* k') (χ : Fin n → G →* kˣ) (η : G →* ℤˣ), Function.Injective j →
      (∀ g, (r g).charpoly.map φ = ∏ i, (X - C (ι (χ i g)))) →
      (∀ g, ((r g).map j).charpoly = ((((η g : ℤˣ) : ℤ) : K) • (r g).map j).charpoly) →
      ∀ i, ∃ i', W.pushCh (Int.castRingHom k) η * χ i = χ i' := by
  intro K k k' B G _ _ _ _ _ n r j φ ι χ η hj h1 h2 i
  have key : ∀ g, Pr.chPoly χ g = Pr.chPoly (fun i => W.pushCh (Int.castRingHom k) η * χ i) g := by
    intro g
    have hv : ∀ i, (((W.pushCh (Int.castRingHom k) η * χ i) g : kˣ) : k) = (((η g : ℤˣ) : ℤ) : k) * (χ i g : k) := by
      intro i
      rfl
    unfold Pr.chPoly
    simp only [hv]
    rcases Int.units_eq_one_or (η g) with e | e
    · simp only [e, Units.val_one, Int.cast_one, one_mul]
    · have h3 : (r g).charpoly = (-r g).charpoly := by
        apply Polynomial.map_injective j hj
        rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, h2 g, e]
        congr 1
        ext a b
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, Matrix.smul_apply, Matrix.map_apply,
          Matrix.neg_apply, map_neg, smul_eq_mul, neg_mul, one_mul]
      have h4 : ((r g).map φ).charpoly = ∏ i, (X - C (ι (χ i g))) := by rw [Matrix.charpoly_map, h1 g]
      have h5 := charpoly_neg_roots_neg _ _ h4
      have h6 : -((r g).map φ) = (-r g).map φ := by
        ext a b
        simp only [Matrix.map_apply, Matrix.neg_apply, map_neg]
      rw [h6, Matrix.charpoly_map, ← h3, h1 g] at h5
      apply Polynomial.map_injective ι ι.injective
      simp only [Polynomial.map_prod, e, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_neg, map_neg] at h5 ⊢
      exact h5
  obtain ⟨σ, hσ⟩ := Pr.charPerm G k n _ _ key
  exact ⟨σ i, hσ i⟩
