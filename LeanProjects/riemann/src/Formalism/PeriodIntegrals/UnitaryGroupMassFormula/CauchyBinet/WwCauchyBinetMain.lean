import Mathlib
import Formalism.PeriodIntegrals.WwCauchyBinet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm

open Matrix Finset

noncomputable section

namespace PI.WwCauchyBinetWork

open PI.WwCauchyBinet

instance fintypeColChoice {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) : Fintype (KM.ColChoice N nu) :=
  inferInstanceAs (Fintype (∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N))

theorem factor_expand {Lt k : Type} [CommRing k] (N : ℕ) (s : Lt) (h : ℕ) (y : Fin N → ℕ → k) :
    Matrix.det (Matrix.of fun i j : Fin h =>
      ∑ a : Fin N, MvPolynomial.C (y a (j : ℕ)) * (MvPolynomial.X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N) k))
    = ∑ I : Fin h ↪o Fin N,
        MvPolynomial.C (Matrix.det (Matrix.of fun i j : Fin h => y (I i) (j : ℕ))) *
        MvPolynomial.map (Int.castRingHom k) (Matrix.det (Matrix.of fun i j : Fin h =>
          (MvPolynomial.X (s, (i : ℕ), I j) : MvPolynomial (Lt × ℕ × Fin N) ℤ))) := by
  have hM : (Matrix.of fun i j : Fin h =>
      ∑ a : Fin N, MvPolynomial.C (y a (j : ℕ)) *
        (MvPolynomial.X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N) k)) =
      (Matrix.of fun (i : Fin h) (a : Fin N) =>
        (MvPolynomial.X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N) k)) *
      (Matrix.of fun (a : Fin N) (j : Fin h) =>
        (MvPolynomial.C (y a (j : ℕ)) : MvPolynomial (Lt × ℕ × Fin N) k)) := by
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  rw [hM, PI.IsoDerivBFintype.cauchyBinet]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [mul_comm]
  congr 1
  · rw [RingHom.map_det]
    congr 1
  · rw [RingHom.map_det]
    congr 1
    ext i j
    simp

theorem wwCauchyBinet_main : WwCauchyBinet := by
  intro Lt _ _ k _ N nu y
  rw [finsum_eq_sum_of_fintype]
  simp only [DeX, factor_expand]
  simp only [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [minY, KM.nablaX, map_prod, Finset.prod_mul_distrib]

end PI.WwCauchyBinetWork
