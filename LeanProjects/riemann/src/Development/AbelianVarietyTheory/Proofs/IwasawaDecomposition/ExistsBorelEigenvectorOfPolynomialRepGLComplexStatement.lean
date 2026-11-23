import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBorelEigenvectorOfPolynomialRepGLComplex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_borelEigenvector_of_polynomialRepGLComplex : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∃ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam := by
  first | exact @GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep | exact GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep | (intros; apply GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep <;> assumption)
