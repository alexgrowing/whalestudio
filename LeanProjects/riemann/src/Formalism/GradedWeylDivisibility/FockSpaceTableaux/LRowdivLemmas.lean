import Formalism.GradedWeylDivisibility.StatementA

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem rowDiv_add (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  simp only [rowDiv, map_add, Polynomial.coeff_add]

theorem rowDiv_smul (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (c : R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]

def rowDivL (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) :
    MvPolynomial (Fin r × Fin n) R →ₗ[R] MvPolynomial (Fin r × Fin n) R where
  toFun := rowDiv R a b k
  map_add' := rowDiv_add R a b k
  map_smul' := rowDiv_smul R a b k

@[simp] theorem rowDivL_apply (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : rowDivL R a b k f = rowDiv R a b k f := rfl

theorem applyWord_nil (R : Type*) [CommRing R] {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R [] f = f := rfl

theorem applyWord_cons (R : Type*) [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ)
    (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) f = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) := rfl

end Formalism.GradedWeylDivisibility
