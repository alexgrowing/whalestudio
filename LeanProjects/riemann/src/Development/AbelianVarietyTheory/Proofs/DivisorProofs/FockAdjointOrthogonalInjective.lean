import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC

noncomputable section
namespace GlobalTheory.FockAdj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem inner_monomial_left (hι : IsFockIP ι) (α : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (monomial α 1)) (ι Q) =
      coeff α Q * α.prod (fun _ k => (k.factorial : ℂ)) := by
  induction Q using MvPolynomial.induction_on' with
  | add Q Q' h h' => simp only [map_add, inner_add_right, h, h', coeff_add, add_mul]
  | monomial β b =>
    have hm : (monomial β b : MvPolynomial σ ℂ) = b • monomial β 1 := by
      rw [smul_monomial]; simp
    rw [coeff_monomial]
    conv_lhs => rw [hm]
    rw [map_smul, inner_smul_right, hι]
    by_cases h : α = β
    · subst h; simp
    · simp [h, Ne.symm h]

theorem inner_eq_zero_of_isHomogeneous (hι : IsFockIP ι) {d e : ℕ} {P Q : MvPolynomial σ ℂ}
    (hde : d ≠ e) (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous e) :
    inner ℂ (ι P) (ι Q) = 0 := by
  rw [P.as_sum, map_sum, sum_inner]
  refine Finset.sum_eq_zero fun α hα => ?_
  have hm : (monomial α (coeff α P) : MvPolynomial σ ℂ) = coeff α P • monomial α 1 := by
    rw [smul_monomial]; simp
  have h0 : coeff α Q = 0 := by
    by_contra hc
    exact hde ((hP (mem_support_iff.mp hα)).symm.trans (hQ hc))
  rw [hm, map_smul, inner_smul_left, inner_monomial_left hι, h0, zero_mul, mul_zero]

theorem injective_of_isFockIP (hι : IsFockIP ι) : Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  ext α
  have h := inner_monomial_left hι α P
  rw [hP, inner_zero_right] at h
  have hne : α.prod (fun _ k => (k.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simpa [hne] using h.symm

theorem fock_adjoint_orthogonal_injective :
    ∀ (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (ι : MvPolynomial σ ℂ →ₗ[ℂ] H), IsFockIP ι →
      (∀ (i : σ) (P Q : MvPolynomial σ ℂ),
        inner ℂ (ι (X i * P)) (ι Q) = inner ℂ (ι P) (ι (pderiv i Q))) ∧
      (∀ (d e : ℕ) (P Q : MvPolynomial σ ℂ), d ≠ e → P ∈ homog σ d → Q ∈ homog σ e →
        inner ℂ (ι P) (ι Q) = 0) ∧ Function.Injective ι :=
  fun _ _ _ _ _ _ hι => ⟨GlobalTheory.FockDeg.inner_X_mul hι,
    fun _ _ _ _ hde hP hQ => inner_eq_zero_of_isHomogeneous hι hde hP hQ,
    injective_of_isFockIP hι⟩

end GlobalTheory.FockAdj
