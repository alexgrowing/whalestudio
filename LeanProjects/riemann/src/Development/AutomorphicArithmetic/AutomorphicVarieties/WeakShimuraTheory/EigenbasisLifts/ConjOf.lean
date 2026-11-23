import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def dmk {K : Type} [CommRing K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (DualNumber K) := Matrix.of fun i j => (⟨A i j, B i j⟩ : DualNumber K)

private theorem dmk_mul {K : Type} [CommRing K] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) K) :
    dmk A B * dmk C D = dmk (A * C) (A * D + B * C) := by
  have hf : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.fst (dmk P Q i j) = P i j := fun _ _ _ _ => rfl
  have hs : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.snd (dmk P Q i j) = Q i j := fun _ _ _ _ => rfl
  ext i j
  · rw [hf, Matrix.mul_apply, TrivSqZeroExt.fst_sum, Matrix.mul_apply]
    simp only [TrivSqZeroExt.fst_mul, hf]
  · rw [hs, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [TrivSqZeroExt.snd_mul, hf, hs, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

private theorem dmk_one {K : Type} [CommRing K] {n : ℕ} :
    dmk (1 : Matrix (Fin n) (Fin n) K) 0 = 1 := by
  have hf : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.fst (dmk P Q i j) = P i j := fun _ _ _ _ => rfl
  have hs : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.snd (dmk P Q i j) = Q i j := fun _ _ _ _ => rfl
  ext i j
  · rw [hf, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · rw [hs, Matrix.one_apply, Matrix.zero_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Ws.Eb.conjOf :
    ∀ {K H : Type} [CommRing K] [Group H] {n : ℕ} (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K) (ρ' : H →* GL (Fin n) (DualNumber K)) (X : Matrix (Fin n) (Fin n) K), IsTan ρ y ρ' → (∀ g, y g = Loc.adGL ρ g X - X) →
        ∃ Q : GL (Fin n) (DualNumber K), ∀ g, ρ' g = Q * W.pushRep (algebraMap K (DualNumber K)) ρ g * Q⁻¹ := by
  intro K H _ _ n ρ y ρ' X hT hy
  unfold IsTan at hT
  have hinv : dmk (1 : Matrix (Fin n) (Fin n) K) (-X) * dmk 1 X = 1 := by
    rw [dmk_mul]
    simp [dmk_one]
  have hinv' : dmk (1 : Matrix (Fin n) (Fin n) K) X * dmk 1 (-X) = 1 := by
    rw [dmk_mul]
    simp [dmk_one]
  refine ⟨⟨dmk 1 (-X), dmk 1 X, hinv, hinv'⟩, fun g => ?_⟩
  have hp : ((W.pushRep (algebraMap K (DualNumber K)) ρ g : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K)) = dmk (ρ g : Matrix (Fin n) (Fin n) K) 0 := by
    ext i j
    · simp [W.pushRep, TrivSqZeroExt.algebraMap_eq_inl]
      rfl
    · simp [W.pushRep, TrivSqZeroExt.algebraMap_eq_inl]
      rfl
  have hyg : y g * (ρ g : Matrix (Fin n) (Fin n) K) = 1 * (ρ g : Matrix (Fin n) (Fin n) K) * X + (1 * 0 + -X * (ρ g : Matrix (Fin n) (Fin n) K)) * 1 := by
    rw [hy g]
    simp only [Loc.adGL, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sub_mul, mul_assoc, ← Matrix.coe_units_inv, Units.inv_mul, mul_one, one_mul, mul_zero, zero_add, neg_mul, sub_eq_add_neg]
    rw [add_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, neg_mul]
  ext i j : 2
  rw [Units.val_mul, Units.val_mul, hp, Units.inv_mk]
  rw [dmk_mul, dmk_mul, hT g i j, ← hyg]
  simp only [one_mul, mul_one]
  rfl
