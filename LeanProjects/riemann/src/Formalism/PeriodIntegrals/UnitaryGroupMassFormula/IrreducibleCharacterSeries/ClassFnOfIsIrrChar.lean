import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.CharacterEqOfRepIso

noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT

namespace PI.SerBridgeGLW

theorem sum_card_fibers {r s : ℕ} (b : Fin r → Fin s) : ∑ j, Fintype.card {i // b i = j} = r := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv b)
  rw [Fintype.card_sigma, Fintype.card_fin] at h
  exact h

end PI.SerBridgeGLW
