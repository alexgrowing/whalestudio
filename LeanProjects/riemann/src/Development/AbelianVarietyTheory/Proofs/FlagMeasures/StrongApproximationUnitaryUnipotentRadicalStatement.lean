import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_unitaryUnipotentRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)), I.IsIsot W → (∃ N : Subgroup I.GA, (N : Set I.GA) = I.NA W) ∧ IsClosed (I.NA W) ∧ (∀ m ∈ I.NA W, ((m.1, 1) : I.GA) ∈ I.NA W ∧ ((1, m.2) : I.GA) ∈ I.NA W) ∧ (∀ U : Set I.Gf, U ∈ nhds (1 : I.Gf) → ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset ∩ I.NA W, (γ⁻¹ * m).2 ∈ U) ∧ ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset ∩ I.NA W, γ⁻¹ * m ∈ Cp := by
  first | exact @GlobalTheory.UnipApprox.strong_approximation | exact GlobalTheory.UnipApprox.strong_approximation | (intros; apply GlobalTheory.UnipApprox.strong_approximation <;> assumption)
