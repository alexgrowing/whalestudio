import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Expand

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.killsLam :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G), D.Kills y →
    ∀ (h : MonoidAlgebra A G) (i : ℕ), 1 ≤ i → i ≤ n → D.lam i (h * y) = 0 := by
  intro n A G _ _ D y hy h i hi1 hin
  have key := UpperTheory.V.AlgebraTools.Det.expand D (h * y) (Polynomial A) 1 Polynomial.X
  have hk := hy (Polynomial A)
    ((Polynomial.X : Polynomial A) • MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A)) h)
  have heq : MonoidAlgebra.single 1 (1 : Polynomial A) +
      (Polynomial.X : Polynomial A) • (MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A))) (h * y) =
      1 + ((Polynomial.X : Polynomial A) • MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A)) h) *
        (MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A))) y := by
    rw [map_mul, smul_mul_assoc, MonoidAlgebra.one_def]
  rw [heq, hk] at key
  have hc := congrArg (fun p : Polynomial A => p.coeff i) key
  simp only [one_pow, mul_one, Polynomial.algebraMap_eq, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] at hc
  rw [Finset.sum_ite_eq] at hc
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hi0 : i ≠ 0 := by omega
  simp only [hmem, if_true, hi0, if_false] at hc
  exact hc.symm
