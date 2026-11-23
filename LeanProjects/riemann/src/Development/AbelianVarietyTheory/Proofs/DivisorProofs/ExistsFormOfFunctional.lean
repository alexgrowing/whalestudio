import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

theorem exists_form_of_functional : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (d : ℕ) (Φ : Pol ι N →ₗ[ℝ] ℝ), ∃ P : Pol ι N, P.IsHomogeneous d ∧ ∀ lam : ι → Fin N → ℝ, ev lam P = Φ (linRoot lam ^ d) := by
  intro ι _ _ N d
  induction d with
  | zero =>
    intro Φ
    refine ⟨C (Φ 1), isHomogeneous_C _ _, fun lam => ?_⟩
    simp [ev]
  | succ d ih =>
    intro Φ
    choose P hP hev using fun x : ι × Fin N => ih (Φ ∘ₗ LinearMap.mulLeft ℝ (-X x : Pol ι N))
    refine ⟨∑ x, X x * P x, ?_, fun lam => ?_⟩
    · refine IsHomogeneous.sum _ _ _ fun x _ => ?_
      have := (isHomogeneous_X ℝ x).mul (hP x)
      rwa [add_comm] at this
    · have h1 : linRoot lam ^ (d + 1) = ∑ x : ι × Fin N, lam x.1 x.2 • (-X x * linRoot lam ^ d) := by
        have h0 : linRoot lam = ∑ x : ι × Fin N, lam x.1 x.2 • (-X x : Pol ι N) := by
          simp [linRoot, smul_eq_C_mul]
        rw [pow_succ']
        conv_lhs => enter [1]; rw [h0]
        rw [Finset.sum_mul]
        simp only [smul_mul_assoc]
      rw [h1, map_sum]
      unfold ev
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have := hev x lam
      unfold ev at this
      rw [map_mul, this, map_smul, eval_X]
      simp

end GlobalTheory.FlagPoly
