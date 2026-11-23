import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_mvPolynomial_ev_eq_act : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), ∃ Φ : TIdx ι d → MvPolynomial (ι × ι) ℚ, ∀ (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) (k : TIdx ι d), ev (Φ k) y = act d (fun k => algebraMap ℚ R (t k)) y k := by
  intro ι _ _ m d t
  refine ⟨fun k => ∑ a : Fin (d k.1) → ι,
    MvPolynomial.C (t ⟨k.1, a⟩) * ∏ i, MvPolynomial.X (a i, k.2 i), ?_⟩
  intro R _ _ y k
  simp [ev, act, tpow, Matrix.vecMul, dotProduct, map_sum, map_prod,
    MvPolynomial.aeval_X]

end GlobalTheory.ClassFin
