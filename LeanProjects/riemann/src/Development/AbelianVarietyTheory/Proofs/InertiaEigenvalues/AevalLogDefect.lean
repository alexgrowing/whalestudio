import Mathlib

noncomputable section

namespace GlobalTheory.LogU

def truncLogF {R : Type} [CommRing R] (n : ℕ) (u : R) : R :=
  ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * u ^ (k + 1)

theorem map_truncLogF {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n : ℕ) (u : R) :
    f (truncLogF n u) = truncLogF n (f u) := by
  simp [truncLogF, map_sum, map_mul, map_pow, map_neg, map_one, map_natCast]

def logDefect (n : ℕ) : MvPolynomial (Fin 2) ℤ :=
  truncLogF n (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 1) -
    truncLogF n (MvPolynomial.X 0) - truncLogF n (MvPolynomial.X 1)

theorem aeval_logDefect {R : Type} [CommRing R] (n : ℕ) (a b : R) :
    MvPolynomial.aeval ![a, b] (logDefect n) = truncLogF n (a + b + a * b) - truncLogF n a - truncLogF n b := by
  have h := fun u => map_truncLogF (MvPolynomial.aeval (R := ℤ) ![a, b]).toRingHom n u
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  simp [logDefect, h]

end GlobalTheory.LogU
