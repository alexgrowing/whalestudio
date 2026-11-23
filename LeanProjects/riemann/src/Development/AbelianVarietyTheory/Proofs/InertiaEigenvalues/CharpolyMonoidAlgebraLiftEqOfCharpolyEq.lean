import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemOfCharpolyCoeffMem
open scoped BigOperators

namespace GlobalTheory

open scoped BigOperators in
open Polynomial in
private lemma det_generic_sum_eq_of_charpoly_eq {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly)
    (m : ℕ) (g : Fin m → G) :
    (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) k) • (ρ (g i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)).det =
      (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) k) • (σ (g i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)).det := by
  ext d
  let T : Subalgebra k (Bool → k) :=
    AlgHom.equalizer (Pi.evalAlgHom k (fun _ : Bool => k) true) (Pi.evalAlgHom k (fun _ : Bool => k) false)
  have key := _root_.GlobalTheory.coeff_det_generic_sum_mem_of_charpoly_coeff_mem T n
    (fun b => if b then ρ else σ) (by intro g j; simp [T, AlgHom.mem_equalizer, h]) m g d
  simpa [T, AlgHom.mem_equalizer] using key

open scoped BigOperators in
open Polynomial in
private lemma charpoly_sum_smul_eq_of_charpoly_eq {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly)
    (m : ℕ) (c : Fin m → k) (g : Fin m → G) :
    (∑ i, c i • ρ (g i)).charpoly = (∑ i, c i • σ (g i)).charpoly := by
  have hd := det_generic_sum_eq_of_charpoly_eq n ρ σ h (m + 1) (Fin.cons 1 g)
  have key : ∀ τ : G →* Matrix (Fin n) (Fin n) k, (∑ i, c i • τ (g i)).charpoly =
      MvPolynomial.aeval (Fin.cons (X : k[X]) (fun i => -C (c i)) : Fin (m + 1) → k[X])
        (∑ i, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) k) •
          (τ ((Fin.cons 1 g : Fin (m + 1) → G) i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin (m + 1)) k)).det := by
    intro τ
    rw [AlgHom.map_det]
    unfold Matrix.charpoly
    congr 1
    ext i j
    simp [Fin.sum_univ_succ, Matrix.charmatrix_apply, Matrix.sum_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  rw [key ρ, key σ, hd]

open scoped BigOperators in
open Polynomial in
theorem _root_.GlobalTheory.charpoly_lift_eq_of_charpoly_eq : ∀ {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ g, (ρ g).charpoly = (σ g).charpoly) →
    ∀ a : MonoidAlgebra k G,
      (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a).charpoly =
      (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G σ a).charpoly := by
  intro k G _ _ n ρ σ h a
  have hsum : ∀ τ : G →* Matrix (Fin n) (Fin n) k,
      MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G τ a =
        ∑ i, a.coeff (a.coeff.support.equivFin.symm i) • τ (a.coeff.support.equivFin.symm i) := by
    intro τ
    rw [MonoidAlgebra.lift_apply, Finsupp.sum, ← Finset.sum_coe_sort a.coeff.support]
    exact (Equiv.sum_comp a.coeff.support.equivFin.symm (fun x : a.coeff.support => a.coeff x • τ x)).symm
  rw [hsum ρ, hsum σ]
  exact charpoly_sum_smul_eq_of_charpoly_eq n ρ σ h _ _ _

end GlobalTheory
