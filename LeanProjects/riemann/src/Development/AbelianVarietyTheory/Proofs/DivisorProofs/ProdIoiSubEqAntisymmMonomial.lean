import Mathlib
open MvPolynomial

namespace GlobalTheory.VandermondeAntisym

theorem prod_Ioi_rev {R : Type*} [CommMonoid R] {n : ℕ} (f : Fin n → Fin n → R) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, f (Fin.rev j) (Fin.rev i)) = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, f i j := by
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun j => Finset.Iio j) (fun i j => by simp [and_comm])]
  rw [← Equiv.prod_comp (Fin.revPerm (n := n))]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [Fin.revPerm_apply]
  rw [← Fin.map_revPerm_Ioi, Finset.prod_map]
  simp

theorem det_eq (n : ℕ) :
    (Matrix.of fun i j : Fin n => (-X i : MvPolynomial (Fin n) ℝ) ^ (n - 1 - (j : ℕ))).det =
      ∏ i : Fin n, ∏ i' ∈ Finset.Ioi i, ((X i' : MvPolynomial (Fin n) ℝ) - X i) := by
  have h : (Matrix.of fun i j : Fin n => (-X i : MvPolynomial (Fin n) ℝ) ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde (fun i : Fin n => (-X (Fin.rev i) : MvPolynomial (Fin n) ℝ))).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
    rw [Nat.sub_sub, Nat.add_comm 1]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde]
  rw [← prod_Ioi_rev]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Fin.rev_rev]; ring

end GlobalTheory.VandermondeAntisym

open GlobalTheory.VandermondeAntisym in

theorem GlobalTheory.prod_Ioi_sub_eq_antisymm_monomial : ∀ n : ℕ, (∏ i : Fin n, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X i' - MvPolynomial.X i) : MvPolynomial (Fin n) ℝ) = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) • rename σ (∏ i : Fin n, (-MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ (n - 1 - (i : ℕ))) := by
  intro n
  rw [← det_eq, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, Int.cast_smul_eq_zsmul ℝ, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp
