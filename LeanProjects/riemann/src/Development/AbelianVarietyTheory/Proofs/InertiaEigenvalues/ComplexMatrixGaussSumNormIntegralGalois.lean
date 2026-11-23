import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumSingularAndInvertible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumMulDualEqCardPowSqStatement

open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem norm_val_monoidHom_units_eq_one {G : Type} [Group G] [Finite G] (ξ : G →* ℂˣ) (g : G) :
    ‖((ξ g : ℂˣ) : ℂ)‖ = 1 := by
  have h : (ξ g) ^ (Nat.card G) = 1 := by rw [← map_pow, pow_card_eq_one']; exact map_one ξ
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card G) ?_ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem isIntegral_int_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    IsIntegral ℤ z :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [h]⟩

theorem isIntegral_val_monoidHom_units {G : Type} [Group G] [Finite G] (ξ : G →* ℂˣ) (g : G) :
    IsIntegral ℤ ((ξ g : ℂˣ) : ℂ) := by
  refine isIntegral_int_of_pow_eq_one (n := Nat.card G) Nat.card_pos ?_
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

theorem isIntegral_addChar_apply {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (x : k) :
    IsIntegral ℤ (ψ x) := by
  refine isIntegral_int_of_pow_eq_one (n := Fintype.card k) Fintype.card_pos ?_
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]

theorem complexMatrixGaussSum_norm_integral_galois :
    ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∀ S : ℂ, S = (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k))) → ‖S‖ ^ 2 = (Fintype.card k : ℝ) ^ (r ^ 2) ∧ IsIntegral ℤ S ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ (r ^ 2) * S⁻¹) ∧ ∀ (τ : ℂ ≃+* ℂ) (ξ' : kˣ →* ℂˣ), (∀ x, ((ξ' x : ℂˣ) : ℂ) = τ ((ξ x : ℂˣ) : ℂ)) → ∃ a : kˣ, (∀ x, τ (ψ x) = ψ ((a : k) * x)) ∧ τ S = ((ξ' a : ℂˣ) : ℂ) ^ r * ∑ x : GL (Fin r) k, (((ξ' (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) := by
  intro k _ _ _ ψ ξ r hψ hξ S hS
  have hN := GlobalTheory.T.matrixGaussSum_mul_dual_eq_card_pow_sq k ℂ ψ ξ r hψ hξ
  simp only [Matrix.one_mul] at hN
  rw [← hS] at hN
  set D := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hD
  have hconj : D = starRingEnd ℂ S := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, AddChar.inv_apply, AddChar.map_neg_eq_conj, MonoidHom.inv_apply, inv_inv,
      Units.val_inv_eq_inv_val, map_inv₀,
      ← Complex.inv_eq_conj (norm_val_monoidHom_units_eq_one ξ _), inv_inv]
  have hDint : IsIntegral ℤ D := by
    refine IsIntegral.sum _ fun x _ => IsIntegral.mul ?_ (isIntegral_addChar_apply _ _)
    exact isIntegral_val_monoidHom_units _ _
  have hSint : IsIntegral ℤ S := by
    rw [hS]
    refine IsIntegral.sum _ fun x _ => IsIntegral.mul ?_ (isIntegral_addChar_apply _ _)
    rw [← map_inv]
    exact isIntegral_val_monoidHom_units _ _
  have hq0 : (Fintype.card k : ℂ) ^ (r ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hS0 : S ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hN
    exact hq0 hN.symm
  refine ⟨?_, hSint, ?_, ?_⟩
  · rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hN
    exact_mod_cast hN
  · rw [← hN, mul_comm S D, mul_assoc, mul_inv_cancel₀ hS0, mul_one]
    exact hDint
  · intro τ ξ' hξ'

    let φ : AddChar k ℂ := (τ : ℂ →+* ℂ).toMonoidHom.compAddChar ψ
    have hbij : Function.Bijective (fun b : k => ψ.mulShift b) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨AddChar.to_mulShift_inj_of_isPrimitive hψ, AddChar.card_eq.symm⟩
    obtain ⟨b, hb⟩ := hbij.2 φ
    have hbφ : ∀ x, τ (ψ x) = ψ (b * x) := fun x => by
      have := DFunLike.congr_fun hb x
      simpa [φ, AddChar.mulShift_apply] using this.symm
    have hb0 : b ≠ 0 := by
      rintro rfl
      have h1 : ψ.mulShift 1 ≠ 1 := hψ one_ne_zero
      apply h1
      ext x
      have := hbφ x
      rw [zero_mul, AddChar.map_zero_eq_one, ← map_one τ] at this
      rw [AddChar.mulShift_apply, one_mul, AddChar.one_apply]
      exact τ.injective this
    have hξ'1 : ξ' ≠ 1 := by
      intro h1
      apply hξ
      ext x
      have := hξ' x
      rw [h1, MonoidHom.one_apply, Units.val_one, ← map_one τ] at this
      exact (τ.injective this).symm
    refine ⟨Units.mk0 b hb0, fun x => hbφ x, ?_⟩
    let g : GL (Fin r) k :=
      Units.map (Matrix.scalar (Fin r) : k →+* Matrix (Fin r) (Fin r) k).toMonoidHom (Units.mk0 b hb0)
    have hg : (g : Matrix (Fin r) (Fin r) k) = Matrix.scalar (Fin r) b := rfl
    have hdet : Matrix.GeneralLinearGroup.det g = (Units.mk0 b hb0) ^ r := by
      ext
      simp [hg, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]
    have key := (GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ ξ' r hψ hξ'1).2 g
    rw [hdet, map_pow, Units.val_pow_eq_pow_val] at key
    simp only [Matrix.one_mul] at key
    rw [← key, hS, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, hbφ, Units.val_inv_eq_inv_val, map_inv₀, ← hξ', ← Units.val_inv_eq_inv_val, hg,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul]

end GlobalTheory
