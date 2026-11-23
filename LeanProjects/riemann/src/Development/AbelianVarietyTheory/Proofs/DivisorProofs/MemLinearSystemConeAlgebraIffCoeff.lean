import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

set_option autoImplicit false

namespace GlobalTheory.DegCmp

theorem X_pow_mul_C_mem_coneAlg {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (d : ℕ) (t : Ω) (ht : t ∈ ((LinearMap.range ev) ^ d : Submodule K Ω)) :
    (Polynomial.X ^ d * Polynomial.C t : Polynomial Ω) ∈ coneAlg ev := by
  induction ht using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [pow_zero, one_mul]
    exact (coneAlg ev).algebraMap_mem r
  | add x y i _ _ hx hy =>
    rw [map_add, mul_add]
    exact add_mem hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨v, rfl⟩ := hm
    have h : (Polynomial.X * Polynomial.C (ev v) : Polynomial Ω) ∈ coneAlg ev := Algebra.subset_adjoin ⟨v, rfl⟩
    have e : (Polynomial.X ^ i.succ * Polynomial.C (ev v * x) : Polynomial Ω) =
        (Polynomial.X * Polynomial.C (ev v)) * (Polynomial.X ^ i * Polynomial.C x) := by
      rw [map_mul, pow_succ]; ring
    rw [e]
    exact mul_mem h hx

theorem mem_coneAlg_iff_coeff : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (p : Polynomial Ω), p ∈ coneAlg ev ↔ ∀ d : ℕ, p.coeff d ∈ ((LinearMap.range ev) ^ d : Submodule K Ω) := by
  intro K V Ω _ _ _ _ _ ev p
  constructor
  · intro hp
    unfold coneAlg at hp
    induction hp using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      intro d
      rcases d with _ | d
      · simp
      · simp only [Polynomial.coeff_X_mul, Polynomial.coeff_C]
        split_ifs with h
        · subst h
          simp
        · exact zero_mem _
    | algebraMap r =>
      intro d
      rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
      split_ifs with h
      · subst h
        rw [pow_zero]
        exact Submodule.algebraMap_mem r
      · exact zero_mem _
    | add x y _ _ hx hy =>
      intro d
      rw [Polynomial.coeff_add]
      exact add_mem (hx d) (hy d)
    | mul x y _ _ hx hy =>
      intro d
      rw [Polynomial.coeff_mul]
      refine Submodule.sum_mem _ fun c hc => ?_
      have hc' : c.1 + c.2 = d := by simpa using hc
      rw [← hc', pow_add]
      exact Submodule.mul_mem_mul (hx _) (hy _)
  · intro h
    rw [p.as_sum_support]
    refine Subalgebra.sum_mem _ fun d _ => ?_
    rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_comm]
    exact X_pow_mul_C_mem_coneAlg ev d _ (h d)

end GlobalTheory.DegCmp
