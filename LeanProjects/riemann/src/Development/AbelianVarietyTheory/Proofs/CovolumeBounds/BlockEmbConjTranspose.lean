import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B GlobalTheory.HCXi

noncomputable section

namespace GlobalTheory.HCXi

theorem blockEmb_conjTranspose (k i r' : ℕ)
    (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    (ιLev k i r' g)ᴴ = ιLev k i r' gᴴ := by
  rw [PI.QnLevBasicsW.ιLev_eq, PI.QnLevBasicsW.ιLev_eq, conjTranspose_submatrix, fromBlocks_conjTranspose]
  simp

theorem blockEmb_mem_Kset : ∀ k r' : ℕ, ∀ y ∈ Kset k r', ιLev k 1 r' y ∈ Kset k (1 + r') := by
  intro k r' y hy
  refine ⟨PI.QnLevBasicsW.level_group_unitary_hermitian k 1 r' y hy.1, ?_⟩
  rw [blockEmb_conjTranspose, ← (PI.QnLevBasicsW.level_group_homomorphism k 1 r').2, hy.2]
  exact (PI.QnLevBasicsW.level_group_homomorphism k 1 r').1

end GlobalTheory.HCXi
