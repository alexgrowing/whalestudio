import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private def borEquiv (K : Type) [Field K] (n : ℕ) (g : GL (Fin n) K) :
    bor g ≃ₗ[K] ({p : Fin n × Fin n // p.1 ≤ p.2} → K) where
  toFun X p := ((g : Matrix (Fin n) (Fin n) K) * X.1 * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p.1.1 p.1.2
  map_add' X Y := by
    funext p
    simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by
    funext p
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Pi.smul_apply,
      RingHom.id_apply]
  invFun f := ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0) * (g : Matrix (Fin n) (Fin n) K), by
    intro i j h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one, Matrix.of_apply, dif_neg (not_le.mpr h)]⟩
  left_inv X := by
    apply Subtype.ext
    have e : (Matrix.of fun i j => if i ≤ j then ((g : Matrix (Fin n) (Fin n) K) * X.1 *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j else 0) =
        (g : Matrix (Fin n) (Fin n) K) * X.1 * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      ext i j
      rw [Matrix.of_apply]
      split_ifs with h
      · rfl
      · exact (X.2 i j (not_le.mp h)).symm
    show ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if i ≤ j then ((g : Matrix (Fin n) (Fin n) K) * X.1 *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j else 0) * (g : Matrix (Fin n) (Fin n) K) = X.1
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  right_inv f := by
    funext p
    show ((g : Matrix (Fin n) (Fin n) K) * (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0) * (g : Matrix (Fin n) (Fin n) K)) *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p.1.1 p.1.2 = f p
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one, Matrix.of_apply, dif_pos p.2]

theorem UpperTheory.V.Fr.pr_bdim :
    ∀ (K : Type) [Field K] (n : ℕ) (g : GL (Fin n) K), 2 * Module.finrank K (bor g) = n * (n + 1) := by
  intro K _ n g
  rw [(borEquiv K n g).finrank_eq, Module.finrank_fintype_fun_eq_card,
    ← Fintype.card_congr (Sym2.sortEquiv (α := Fin n)), Sym2.card, Fintype.card_fin, Nat.choose_two_right,
    Nat.add_sub_cancel, Nat.mul_comm (n + 1) n]
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd
