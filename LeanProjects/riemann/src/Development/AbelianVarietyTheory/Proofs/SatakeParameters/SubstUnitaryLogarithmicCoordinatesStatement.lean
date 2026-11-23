import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinates
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_unitary_logarithmic_coordinates : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (γ : n → m → MaximalUnramifiedExtension p), (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) → (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) → ∀ Θ : MvPowerSeries n ℂ_[p], HostLog p g2 g3 s2 ε Θ → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) := by
  first | exact @GlobalTheory.KerStd.HostLog.subst_unitary | exact GlobalTheory.KerStd.HostLog.subst_unitary | (intros; apply GlobalTheory.KerStd.HostLog.subst_unitary <;> assumption)
