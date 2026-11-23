import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CharPerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem charpoly_neg {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    (-M).charpoly = (-1) ^ n * M.charpoly.comp (-X) := by
  have h : (M.charmatrix).map (Polynomial.compRingHom (-X : R[X])) = -(-M).charmatrix := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [charmatrix_apply_eq]
      ring
    · simp [charmatrix_apply_ne _ _ _ hij]
  have h2 : M.charpoly.comp (-X) = (-1) ^ n * (-M).charpoly := by
    rw [Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, RingHom.map_det, RingHom.mapMatrix_apply, h,
      det_neg, Fintype.card_fin]
    rfl
  rw [h2, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

private theorem charpoly_comp_neg_roots {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) :
    (-1 : R[X]) ^ n * (∏ i, (X - C (a i))).comp (-X) = ∏ i, (X - C (-a i)) := by
  rw [Polynomial.prod_comp, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [sub_comp, X_comp, C_comp, map_neg]
  ring

theorem UpperTheory.V.Th.Det.perm4 :
    ∀ (K k B G : Type) [Field K] [Field k] [CommRing B] [Group G] (n : ℕ) (r : G →* GL (Fin n) K) (j : B →+* K) (φ : B →+* k) (χ : Fin n → G →* kˣ) (η : G →* ℤˣ), Function.Injective j → Pr.RedTo r j φ χ → (∀ g, (W.mat r g).charpoly = ((((η g : ℤˣ) : ℤ) : K) • W.mat r g).charpoly) → ∀ i, ∃ i', W.pushCh (Int.castRingHom k) η * χ i = χ i' := by
  intro K k B G _ _ _ _ n r j φ χ η hj hred hsym
  let χ' : Fin n → G →* kˣ := fun i => W.pushCh (Int.castRingHom k) η * χ i
  have hval : ∀ g i, (((χ' i) g : kˣ) : k) = (((η g : ℤˣ) : ℤ) : k) * ((χ i g : kˣ) : k) := by
    intro g i
    simp [χ', W.pushCh]
  have key : ∀ g, Pr.chPoly χ g = Pr.chPoly χ' g := by
    intro g
    rcases Int.units_eq_one_or (η g) with h | h
    · unfold Pr.chPoly
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hval g i, h]
      simp
    · obtain ⟨p, hp1, hp2⟩ := hred g
      have hp1' : Polynomial.map j p = (W.mat r g).charpoly := hp1
      have hM : (W.mat r g).charpoly = (-1) ^ n * (W.mat r g).charpoly.comp (-X) := by
        rw [← charpoly_neg, hsym g, h, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
          neg_one_smul]
      have hp : p = (-1) ^ n * p.comp (-X) := by
        apply Polynomial.map_injective j hj
        rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
          Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X, hp1']
        exact hM
      have hq := congrArg (Polynomial.map φ) hp
      rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
        Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X, hp2] at hq
      rw [hq]
      unfold Pr.chPoly
      rw [charpoly_comp_neg_roots (fun i => (((χ i) g : kˣ) : k))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hval g i, h]
      simp
  obtain ⟨σ, hσ⟩ := Pr.charPerm G k n χ χ' key
  intro i
  exact ⟨σ i, hσ i⟩
