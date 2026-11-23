import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsStagesWithDelta
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stages_with_delta : ∀ (B : Base) (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool) (η : ℝ), 0 < Del → 0 < η → Function.Injective letter → (∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) → (∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ = (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)) → ∃ X : Stages, X.B = B ∧ X.toD7.s.Del = Del ∧ X.toD7.div.etaF = η ∧ DV.KapDef X.toD7 ∧ ∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0 := by
  first | exact @GlobalTheory.StandInStages.exists_stages_prescribed | exact GlobalTheory.StandInStages.exists_stages_prescribed | (intros; apply GlobalTheory.StandInStages.exists_stages_prescribed <;> assumption)
