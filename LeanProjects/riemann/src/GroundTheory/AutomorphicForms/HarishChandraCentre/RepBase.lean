import Mathlib

namespace GroundTheory.Automorphic.HarishChandra

abbrev Poly (n : ℕ) := MvPolynomial (Fin n × Fin n) ℂ

variable {n : ℕ}

noncomputable def rowOp (i j : Fin n) : Module.End ℂ (Poly n) :=
  ∑ k : Fin n, (LinearMap.mulLeft ℂ (MvPolynomial.X (i, k) : Poly n)) ∘ₗ
    (MvPolynomial.pderiv (j, k) : Derivation ℂ (Poly n) (Poly n)).toLinearMap

theorem rowOp_apply (i j : Fin n) (f : Poly n) :
    rowOp i j f = ∑ k : Fin n, MvPolynomial.X (i, k) * MvPolynomial.pderiv (j, k) f := by
  simp [rowOp, LinearMap.sum_apply]

end GroundTheory.Automorphic.HarishChandra
