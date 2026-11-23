import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FinrankUperpOfDet

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

lemma isHerm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    (gramM k r z z' g).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [gramM]
  exact (ggHerm_swap _ (Formalism.QuantumDeterminants.GBasic.Hpk_herm k r) _ _).symm

def PosCount : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 →
    Fintype.card {i // 0 < (isHerm k r z z' γ).eigenvalues i} ≤ r + 1

def NonposCount : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    (gramM k r z z' γ).det ≠ 0 →
    Fintype.card {i // ¬ 0 < (isHerm k r z z' γ).eigenvalues i} ≤ r + 1

end PI.FrameInd
