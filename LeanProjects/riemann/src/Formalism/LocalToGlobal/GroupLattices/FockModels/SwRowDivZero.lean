import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.GradedWeylDivisibility

variable (R : Type) [CommRing R] {r n : ℕ}

def Dop (a b : Fin r) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.1 = b then X (a, v.2) else 0

theorem Dop_X (a b : Fin r) (v : Fin r × Fin n) :
    Dop R a b (X v) = if v.1 = b then X (a, v.2) else 0 :=
  MvPolynomial.mkDerivation_X R _ v

def DL (a b : Fin r) : Module.End R (MvPolynomial (Fin r × Fin n) R) := (Dop R a b).toLinearMap

theorem DL_apply (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) : DL R a b f = Dop R a b f := rfl

theorem sw_rowGen_X (a b : Fin r) (v : Fin r × Fin n) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  exact rowGen_X R a b v

theorem sw_rowGen_C (a b : Fin r) (c : R) :
    rowGen R a b (C c : MvPolynomial (Fin r × Fin n) R) = Polynomial.C (C c) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]

theorem sw_deriv (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    (1 + if a = b then Polynomial.X else 0) * Polynomial.derivative (rowGen R a b f) =
      rowGen R a b (Dop R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [sw_rowGen_C, Polynomial.derivative_C, mul_zero, MvPolynomial.derivation_C, map_zero]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, map_add, mul_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add,
      map_mul, map_mul, ← hp, Dop_X, sw_rowGen_X]
    by_cases h1 : v.1 = b <;> by_cases h2 : a = b <;>
      simp only [h1, h2, if_true, if_false, sw_rowGen_X, map_zero, mul_zero, zero_mul, add_zero,
        Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
        Polynomial.derivative_X, zero_add, one_mul, mul_one, Polynomial.derivative_zero] <;> ring

theorem sw_rowDiv_zero (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) R) : rowDiv R a b 0 g = g := by
  unfold rowDiv
  induction g using MvPolynomial.induction_on with
  | C c => rw [sw_rowGen_C, Polynomial.coeff_C_zero]
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp, sw_rowGen_X]
    split_ifs <;> simp

theorem sw_step_ne (a b : Fin r) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k + 1 : ℕ) : R) • rowDiv R a b (k + 1) f = rowDiv R a b k (Dop R a b f) := by
  have h := sw_deriv R a b f
  rw [if_neg hab, add_zero, one_mul] at h
  unfold rowDiv
  rw [← h, Polynomial.coeff_derivative, MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 1
  simp

theorem sw_step_eq (a : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k + 1 : ℕ) : R) • rowDiv R a a (k + 1) f =
      rowDiv R a a k (Dop R a a f) - (k : R) • rowDiv R a a k f := by
  have h := sw_deriv R a a f
  rw [if_pos rfl] at h
  unfold rowDiv
  rw [← h, add_mul, one_mul, Polynomial.coeff_add]
  cases k with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero, add_zero, Polynomial.coeff_derivative]
    simp [MvPolynomial.smul_eq_C_mul, mul_comm]
  | succ k =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    simp only [MvPolynomial.smul_eq_C_mul]
    push_cast
    simp only [map_add, map_natCast, map_one]
    ring

theorem sw_pow_ne (a b : Fin r) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k.factorial : ℕ) : R) • rowDiv R a b k f = (DL R a b ^ k) f := by
  induction k generalizing f with
  | zero => simp [sw_rowDiv_zero]
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm, mul_smul, sw_step_ne R a b hab k f, ih,
      pow_succ, Module.End.mul_apply, DL_apply]

theorem sw_pow_eq (a : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k.factorial : ℕ) : R) • rowDiv R a a k f =
      (((List.range k).map fun j : ℕ => DL R (n := n) a a -
        (j : R) • (1 : Module.End R (MvPolynomial (Fin r × Fin n) R))).prod) f := by
  induction k generalizing f with
  | zero => simp [sw_rowDiv_zero]
  | succ k ih =>
    have step : ((k + 1 : ℕ) : R) • rowDiv R a a (k + 1) f =
        rowDiv R a a k ((DL R (n := n) a a - (k : R) • (1 : Module.End R (MvPolynomial (Fin r × Fin n) R))) f) := by
      rw [sw_step_eq R a k f, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, DL_apply,
        sub_eq_add_neg ((Dop R a a) f), rowDiv_add, ← neg_smul, rowDiv_smul, neg_smul, sub_eq_add_neg]
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm, mul_smul, step, ih, List.range_succ,
      List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, Module.End.mul_apply]

theorem sw_rel (a b c d : Fin r) :
    DL R (n := n) a b * DL R c d - DL R c d * DL R a b =
      (if b = c then DL R a d else 0) - (if d = a then DL R c b else 0) := by
  have hder : ⁅Dop R (n := n) a b, Dop R (n := n) c d⁆ =
      (if b = c then Dop R (n := n) a d else 0) - (if d = a then Dop R (n := n) c b else 0) := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply, Dop_X, Dop_X, apply_ite (Dop R (n := n) a b),
      apply_ite (Dop R (n := n) c d), map_zero, map_zero, Dop_X, Dop_X]
    by_cases h1 : v.1 = d <;> by_cases h2 : v.1 = b <;> by_cases h3 : b = c <;>
      by_cases h4 : d = a <;> simp [h1, h2, h3, h4, Dop_X, @eq_comm _ c b, @eq_comm _ a d]
  refine LinearMap.ext fun f => ?_
  have h := congrArg (fun D : Derivation R _ _ => D f) hder
  simp only [Derivation.commutator_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, DL_apply]
  rw [h]
  split_ifs <;> simp [DL_apply]

end Formalism.L2.G.Model
