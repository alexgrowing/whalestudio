import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
open IsLocalRing

namespace GlobalTheory

theorem span_range_X_eq_ker_constantCoeff (k : Type) [Field k] (n : ℕ) :
    Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))
      = RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have key : ∀ q : MvPolynomial (Fin n) k, q - MvPolynomial.C (MvPolynomial.constantCoeff q) ∈
        Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k))) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
        have := Ideal.add_mem _ hp hq
        convert this using 1
        simp only [map_add]; ring
      | mul_X p i _ =>
        simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    simpa [hp] using key p

theorem le_height_span_range_X_mvPolynomial : ∀ (k : Type) [Field k] (n : ℕ), ((n : ℕ∞)) ≤ (Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))).height := by
  intro k _ n
  rw [span_range_X_eq_ker_constantCoeff]
  haveI : (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, by simp⟩)
  have h := ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k))
  exact h.2.ge

end GlobalTheory
