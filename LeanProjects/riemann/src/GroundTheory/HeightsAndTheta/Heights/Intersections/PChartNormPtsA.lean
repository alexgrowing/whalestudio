import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace ChartNormPts

theorem aeval_smul_homog {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
    (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a) (c : K → R) (z : (Σ k, ι k) → R) :
    aeval (fun p => c p.1 * z p) f = (∏ k, c k ^ a k) * aeval z f := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), c i.1 ^ d i) = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

variable {P : Type*} {Q : Type*} [Fintype Q] {V : Type*}

def homogenise (v : P → V) (f g : Q → V) (F : MvPolynomial Q (MvPolynomial P ℤ)) : MvPolynomial V ℤ :=
  ∑ μ ∈ F.support, rename v (F.coeff μ) * ∏ q, X (f q) ^ μ q * X (g q) ^ (degreeOf q F - μ q)

theorem aeval_homogenise {R : Type*} [CommRing R] (v : P → V) (f g : Q → V)
    (F : MvPolynomial Q (MvPolynomial P ℤ)) (z : V → R) :
    aeval z (homogenise v f g F) =
      ∑ μ ∈ F.support, aeval (z ∘ v) (F.coeff μ) * ∏ q, z (f q) ^ μ q * z (g q) ^ (degreeOf q F - μ q) := by
  simp [homogenise, aeval_rename]

theorem aeval_homogenise_div {L : Type*} [Field L] (v : P → V) (f g : Q → V)
    (F : MvPolynomial Q (MvPolynomial P ℤ)) (x : V → L) (hx : ∀ q, x (g q) ≠ 0) :
    aeval x (homogenise v f g F) =
      (∏ q, x (g q) ^ degreeOf q F) *
        eval₂ (aeval (x ∘ v) : MvPolynomial P ℤ →ₐ[ℤ] L).toRingHom (fun q => x (f q) / x (g q)) F := by
  rw [aeval_homogenise, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [div_pow, ← pow_mul_pow_sub (x (g q)) (monomial_le_degreeOf q hμ)]
  field_simp [pow_ne_zero _ (hx q)]

theorem aeval_homogenise_one {R : Type*} [CommRing R] (v : P → V) (f g : Q → V)
    (F : MvPolynomial Q (MvPolynomial P ℤ)) (z : V → R) (hz : ∀ q, z (g q) = 1) :
    aeval z (homogenise v f g F) =
      eval₂ (aeval (z ∘ v) : MvPolynomial P ℤ →ₐ[ℤ] R).toRingHom (fun q => z (f q)) F := by
  rw [aeval_homogenise, eval₂_eq']
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp [hz]

end ChartNormPts

end GroundTheory.Heights₂.Heights.Inter
