import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FBridge

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem psiM_polar {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε)
    (z : PCoord ε → ℂ) :
    PsiM T μ (toMK k * NormedSpace.exp (pmat z)) = T.op k * psM T μ (NormedSpace.exp (pmat z)) := by
  have hX := pmat_inP z
  have hex : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧
      toMK k * NormedSpace.exp (pmat z) = toMK k' * NormedSpace.exp X' := ⟨k, pmat z, hX, rfl⟩
  unfold PsiM
  rw [dif_pos hex]
  obtain ⟨hP, hEq⟩ := hex.choose_spec.choose_spec
  obtain ⟨h1, h2⟩ := polar_unique hX hP hEq
  rw [← h2, ← h1]

theorem psiM_exp_pmat {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    (z : PCoord ε → ℂ) : PsiM T μ (NormedSpace.exp (pmat z)) = psM T μ (NormedSpace.exp (pmat z)) := by
  have h := psiM_polar T μ (1 : KG ε) z
  have e : toMK (1 : KG ε) = 1 := rfl
  have o : T.op (1 : KG ε) = 1 := by simp [KType.op, map_one]
  rwa [e, Matrix.one_mul, o, one_mul] at h

end ReciprocityTheory.ChartRestriction.DS
