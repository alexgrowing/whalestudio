import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementH
import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def transposeVariables (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n × Fin n) R := rename Prod.swap

theorem transposeVariables_involutive (R : Type*) [CommRing R] (n : ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    transposeVariables R n (transposeVariables R n f) = f := by
  simp only [transposeVariables, AlgHom.coe_comp, Function.comp_apply, MvPolynomial.rename_rename]
  have h : (Prod.swap ∘ Prod.swap : Fin n × Fin n → Fin n × Fin n) = id := by
    funext x
    simp
  rw [h]
  exact MvPolynomial.rename_id_apply f

theorem qn_T_X (R : Type*) [CommRing R] (n : ℕ) (l a : Fin n) : transposeVariables R n (X (l, a)) = X (a, l) := by
  simp [transposeVariables]

theorem qn_T_map (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    transposeVariables ℚ n (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℚ) (transposeVariables ℤ n f) := by
  simp only [transposeVariables]
  exact (MvPolynomial.map_rename _ _ _).symm

def qn_D (n : ℕ) (a b : Fin n) :
    Derivation ℚ (MvPolynomial (Fin n × Fin n) ℚ) (MvPolynomial (Fin n × Fin n) ℚ) :=
  ∑ l : Fin n, (X (l, a) : MvPolynomial (Fin n × Fin n) ℚ) • pderiv (l, b)

theorem qn_D_apply (n : ℕ) (a b : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    qn_D n a b f = ∑ l : Fin n, X (l, a) * pderiv (l, b) f := by
  unfold qn_D
  have h := map_sum (Derivation.coeFnAddMonoidHom (R := ℚ) (A := MvPolynomial (Fin n × Fin n) ℚ)
    (M := MvPolynomial (Fin n × Fin n) ℚ)) (fun l : Fin n => (X (l, a) : MvPolynomial (Fin n × Fin n) ℚ) • pderiv (l, b))
    Finset.univ
  have h2 := congrFun h f
  simp only [Finset.sum_apply] at h2
  exact h2.trans (Finset.sum_congr rfl fun l _ => by simp [Derivation.coeFnAddMonoidHom, smul_eq_mul])

theorem qn_E_eq (n : ℕ) (a b : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    glOps ℚ n (rowLetters n) Set.univ a b f = qn_D n a b f := by
  rw [qn_D_apply]
  simp [glOps, glAct, rowLetters, LinearMap.sum_apply]

theorem qn_D_X (n : ℕ) (a b : Fin n) (l c : Fin n) :
    qn_D n a b (X (l, c)) = if c = b then X (l, a) else 0 := by
  rw [qn_D_apply]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq]
  by_cases hc : c = b
  · subst hc
    simp
  · simp [hc]

theorem qn_deriv_rowGen (n : ℕ) (a b : Fin n) (hab : a ≠ b) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    Polynomial.derivative (rowGen ℚ a b (transposeVariables ℚ n f)) = rowGen ℚ a b (transposeVariables ℚ n (qn_D n a b f)) := by
  have hX : ∀ i : Fin n × Fin n, Polynomial.derivative (rowGen ℚ a b (transposeVariables ℚ n (X i))) =
      rowGen ℚ a b (transposeVariables ℚ n (qn_D n a b (X i))) := by
    rintro ⟨l, c⟩
    rw [qn_D_X, qn_T_X]
    by_cases hc : c = b
    · subst hc
      simp [rowGen, qn_T_X, hab]
    · simp [rowGen, hc]
  induction f using MvPolynomial.induction_on with
  | C r =>
    have hD : qn_D n a b (C r) = 0 := by
      rw [qn_D_apply]
      simp
    rw [hD]
    simp [transposeVariables, rowGen]
  | add p q hp hq =>
    simp only [map_add, Polynomial.derivative_add, hp, hq]
  | mul_X p i hp =>
    have hL : qn_D n a b (p * X i) = p * qn_D n a b (X i) + X i * qn_D n a b p := by
      rw [Derivation.leibniz]
      simp [smul_eq_mul]
    rw [hL]
    simp only [map_add, map_mul, Polynomial.derivative_mul, hp, hX i]
    ring

theorem qn_deriv_rowGen_diag (n : ℕ) (a : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    (1 + Polynomial.X) * Polynomial.derivative (rowGen ℚ a a (transposeVariables ℚ n f)) =
      rowGen ℚ a a (transposeVariables ℚ n (qn_D n a a f)) := by
  have hX : ∀ i : Fin n × Fin n, (1 + Polynomial.X) * Polynomial.derivative (rowGen ℚ a a (transposeVariables ℚ n (X i))) =
      rowGen ℚ a a (transposeVariables ℚ n (qn_D n a a (X i))) := by
    rintro ⟨l, c⟩
    rw [qn_D_X, qn_T_X]
    by_cases hc : c = a
    · subst hc
      simp [rowGen, qn_T_X]
      ring
    · simp [rowGen, hc]
  induction f using MvPolynomial.induction_on with
  | C r =>
    have hD : qn_D n a a (C r) = 0 := by
      rw [qn_D_apply]
      simp
    rw [hD]
    simp [transposeVariables, rowGen]
  | add p q hp hq =>
    simp only [map_add, Polynomial.derivative_add, mul_add, hp, hq]
  | mul_X p i hp =>
    have hL : qn_D n a a (p * X i) = p * qn_D n a a (X i) + X i * qn_D n a a p := by
      rw [Derivation.leibniz]
      simp [smul_eq_mul]
    rw [hL, map_mul, map_mul, Polynomial.derivative_mul, mul_add, ← mul_assoc,
      mul_left_comm (1 + Polynomial.X) (rowGen ℚ a a (transposeVariables ℚ n p)), hp, hX i]
    simp only [map_add, map_mul]
    ring

end Formalism.InvariantFactorPaths.ColumnFamilies
