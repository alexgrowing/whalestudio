import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem tor_conj_apply {R : Type} [CommRing R] (t : Rˣ) (Y : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    ((tor R t).val * Y * (tor R t⁻¹).val) a b =
      ((t ^ wt1 a : Rˣ) : R) * Y a b * ((t⁻¹ ^ wt1 b : Rˣ) : R) := by
  rw [tor_val, tor_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem tor_mul_inv {R : Type} [CommRing R] (t : Rˣ) :
    (tor R t⁻¹).val * (tor R t).val = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

private theorem tor_mul_inv' {R : Type} [CommRing R] (t : Rˣ) :
    (tor R t).val * (tor R t⁻¹).val = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem UpperTheory.V.UnitaryThreeInertia.canon_map :
    (∀ {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R), Canon X h → Canon (X.map φ) (GeneralLinearGroup.map φ h)) ∧
    ∀ {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R) (t : Rˣ), Canon X h → Canon ((tor R t).val * X * (tor R t⁻¹).val) (tor R t * h * tor R t⁻¹) := by
  refine ⟨fun {R R'} _ _ _ _ φ _ X h H => ⟨fun a b => ?_, fun a => ?_, ?_⟩,
    fun {R} _ _ X h t H => ⟨fun a b => ?_, fun a => ?_, ?_⟩⟩
  · have e : ((GeneralLinearGroup.map φ h : GL (Fin 3) R').val - 1) a b = φ ((h.val - 1) a b) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one]; rfl
      · rw [map_zero]; rfl
    rw [e]
    exact map_nonunit φ _ (H.hat a b)
  · show φ (h.val a a) = 1
    rw [H.one, map_one]
  · have e : ((GeneralLinearGroup.map φ h)⁻¹ : GL (Fin 3) R').val * X.map φ * (GeneralLinearGroup.map φ h).val =
        ((h⁻¹ : GL (Fin 3) R).val * X * h.val).map φ := by
      rw [Matrix.map_mul, Matrix.map_mul, ← map_inv]; rfl
    rw [e]
    exact H.diag.map (map_zero φ)
  · have e : (tor R t * h * tor R t⁻¹).val - 1 = (tor R t).val * (h.val - 1) * (tor R t⁻¹).val := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, tor_mul_inv', Units.val_mul, Units.val_mul]
    rw [e, tor_conj_apply]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (H.hat a b))
  · rw [Units.val_mul, Units.val_mul, tor_conj_apply, H.one, mul_one, ← Units.val_mul, ← mul_zpow,
      mul_inv_cancel, _root_.one_zpow, Units.val_one]
  · have e : ((tor R t * h * tor R t⁻¹)⁻¹ : GL (Fin 3) R).val * ((tor R t).val * X * (tor R t⁻¹).val) *
        (tor R t * h * tor R t⁻¹).val = (tor R t).val * ((h⁻¹ : GL (Fin 3) R).val * X * h.val) * (tor R t⁻¹).val := by
      have hc : ∀ Y : Matrix (Fin 3) (Fin 3) R, (tor R t⁻¹).val * ((tor R t).val * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, tor_mul_inv, Matrix.one_mul]
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, ← map_inv, inv_inv]
      simp only [Units.val_mul, Matrix.mul_assoc, hc]
    rw [e]
    intro a b hab
    rw [tor_conj_apply, H.diag hab, mul_zero, zero_mul]
