import Formalism.FockGram.StatementFock

open Finset Matrix MvPolynomial

noncomputable section

namespace Formalism.E

section SlopeTestRemainingChoices

variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

def spLin (A : Matrix σ σ R) (i : σ) : MvPolynomial σ R := ∑ j, C (A i j) * X j

def spRow (A : Matrix σ σ R) (s : Multiset σ) : MvPolynomial σ R := (s.map (spLin A)).prod

def spHom (A : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := aeval (spLin A)

end SlopeTestRemainingChoices

section Field

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K] [CharZero K]

end Field

def genMat (σ : Type*) : Matrix σ σ (MvPolynomial (σ × σ) ℤ) := Matrix.of fun i j => X (i, j)

end Formalism.E
