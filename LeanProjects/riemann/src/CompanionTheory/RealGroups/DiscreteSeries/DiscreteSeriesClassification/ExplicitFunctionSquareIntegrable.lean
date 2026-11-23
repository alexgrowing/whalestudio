import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset

noncomputable section

open Finset MeasureTheory Matrix

namespace CompanionTheory.RgDs

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def phi (x : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∏ i : Fin n, ((lead ((i : ℕ) + 1) (xᴴ * x)).re ^ 2)⁻¹

theorem phi_one : phi (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold phi lead
  refine Finset.prod_eq_one fun i _ => ?_
  rw [dif_pos (Nat.succ_le_of_lt i.2)]
  simp [Matrix.submatrix_one _ (Fin.castLE_injective _)]

def FinVol : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (ν : Measure (UJ ε)), ν.IsHaarMeasure →
    ∫⁻ x : UJ ε, ENNReal.ofReal (phi (toM x)) ∂ν < ⊤

def ExplicitFunctionSquareIntegrable : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ),
    IsHCParam lam → IsMu lam μ → ∀ ν : Measure (UJ ε), ν.IsHaarMeasure →
      MemLp (fun g : UJ ε => PsiM T μ (toM g)) 2 ν

end CompanionTheory.RgDs
