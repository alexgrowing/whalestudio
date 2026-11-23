import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.BlockSphereMeanLinForm

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

def lineVanishingIdeal {k : Type} [Field k] {N : ℕ} (y : Fin N → k) : Ideal (MvPolynomial (Fin N) k) :=
  (Ideal.homogeneousCore (homogeneousSubmodule (Fin N) k)
    (vanishingIdeal k (Submodule.span k {y} : Set (Fin N → k)))).toIdeal

theorem aeval_smul_of_isHomogeneous {k K : Type} [Field k] [Field K] [Algebra k K] {N d : ℕ}
    {g : MvPolynomial (Fin N) k} (hg : g.IsHomogeneous d) (t : K) (z : Fin N → K) :
    aeval (t • z) g = t ^ d * aeval z g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h := hg (mem_support_iff.1 hs)
  have hd : ∑ i, s i = d := by
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

set_option autoImplicit false in
open MvPolynomial NumberField in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma linForm_isHomogeneous_one' {K : Type} [Field K] {N : ℕ} (c : Fin N → K) :
    (_root_.GlobalTheory.ChowHt.Model.linForm c).IsHomogeneous 1 := by
  unfold _root_.GlobalTheory.ChowHt.Model.linForm
  refine IsHomogeneous.sum _ _ _ fun j _ => ?_
  simpa using (isHomogeneous_C (Fin 1 × Fin N) (c j)).mul (isHomogeneous_X K ((0 : Fin 1), j))

set_option autoImplicit false in
open MvPolynomial NumberField in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem _root_.GlobalTheory.ChowHt.irreducible_linForm {K : Type} [Field K] {N : ℕ} {c : Fin N → K}
    (hc : c ≠ 0) :
    Irreducible (_root_.GlobalTheory.ChowHt.Model.linForm c) := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hc
  have hk' : (_root_.GlobalTheory.ChowHt.Model.linForm c).coeff (Finsupp.single (0, k) 1) ≠ 0 := by
    rw [_root_.GlobalTheory.ChowHt.Model.coeff_linForm]; exact hk
  have hne : _root_.GlobalTheory.ChowHt.Model.linForm c ≠ 0 := by
    intro h; rw [h, coeff_zero] at hk'; exact hk' rfl
  refine irreducible_of_totalDegree_eq_one
    ((linForm_isHomogeneous_one' c).totalDegree hne) fun x hx => ?_
  refine isUnit_iff_ne_zero.mpr fun hx0 => hk' ?_
  have := hx (Finsupp.single (0, k) 1)
  rw [hx0] at this
  exact zero_dvd_iff.mp this

end GlobalTheory.ChowHt
