import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem exists_mvPolynomial_pick_point :
    ∀ (S : Type) (T : Finset (S → ℂ)) (p : S → ℂ), ∃ Q : MvPolynomial S ℂ,
      MvPolynomial.eval p Q = 1 ∧ ∀ t ∈ T, t ≠ p → MvPolynomial.eval t Q = 0 := by
  classical
  intro S T p
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a T _ ih =>
    obtain ⟨Q, hQ1, hQ0⟩ := ih
    by_cases hap : a = p
    · refine ⟨Q, hQ1, fun t ht htp => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact absurd hap htp
      · exact hQ0 t ht htp
    · obtain ⟨s, hs⟩ := Function.ne_iff.1 hap
      have hne : p s - a s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
      refine ⟨Q * (MvPolynomial.C (p s - a s)⁻¹ * (MvPolynomial.X s - MvPolynomial.C (a s))),
        ?_, fun t ht htp => ?_⟩
      · simp only [map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, hQ1, one_mul]
        exact inv_mul_cancel₀ hne
      · rcases Finset.mem_insert.1 ht with rfl | ht
        · simp
        · simp [hQ0 t ht htp]

end GlobalTheory.QFam
