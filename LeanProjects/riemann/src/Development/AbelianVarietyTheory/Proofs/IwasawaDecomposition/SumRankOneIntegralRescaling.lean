import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIsIntegralIwasawaDecompositionStatement
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem scaleDecomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N)
    (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, cc (t j) = t j) →
    ∃ (k : ℕ) (ξ' : Fin d → Fin N → E) (s : Fin d → E), 0 < k ∧ (∀ j, ξ' j ∈ X.Λ) ∧
      (∀ j, ∃ a : E, ξ' j = a • ξ j) ∧ (∀ j, cc (s j) = s j) ∧ (∀ j, IsIntegral ℤ (s j)) ∧
      (k : E) • (∑ j, (t j * X.κ0) • rk1 X.Gm (ξ j) (ξ j)) =
        ∑ j, (X.m * s j * X.κ0) • rk1 X.Gm (ξ' j) (ξ' j) := by
  intro E _ _ _ N X d ξ t ht
  choose a ha hmem using fun j => GlobalTheory.T.exists_nat_smul_mem_lattice' E N X (ξ j)
  obtain ⟨b, hb, hint⟩ := GlobalTheory.T.exists_common_denominator_isIntegral E d (fun j => t j / ((a j : ℕ) : E) ^ 2)
  have ha0 : ∀ j, ((a j : ℕ) : E) ≠ 0 := fun j => Nat.cast_ne_zero.2 (ha j).ne'
  refine ⟨X.m * b, fun j => ((a j : ℕ) : E) • ξ j, fun j => (b : E) * (t j / ((a j : ℕ) : E) ^ 2),
    Nat.mul_pos X.m_pos hb, hmem, fun j => ⟨_, rfl⟩, ?_, hint, ?_⟩
  · intro j
    rw [cc_mul, div_eq_mul_inv, cc_mul, cc_inv, cc_pow, cc_natCast, cc_natCast, ht, ← div_eq_mul_inv]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rk1_smul_left, rk1_smul_right, cc_natCast, smul_smul, smul_smul, smul_smul]
    congr 1
    have := ha0 j
    push_cast
    field_simp

end GlobalTheory.UnipKill
