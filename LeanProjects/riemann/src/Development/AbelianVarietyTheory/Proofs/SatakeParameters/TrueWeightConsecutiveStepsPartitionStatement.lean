import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetLL
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.KerJ NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueWeight_consecutive_steps_partition : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (i : ℕ), i < D.R.m → ∃ n : D.what₂.Tau → ℕ, (∀ τ r, (lamTG M i τ).natW r + n τ = nuT D u i τ r) ∧ (∀ τ, (lamTG M i τ).detShift + C.sSharp i τ = n τ) ∧ (∀ τ r, (lamTG M (i + 1) τ).natW r = extNu (D.R.N (i + 1)) (fun τ r => (lamTG M i τ).natW r + n τ) τ r) ∧ ∀ τ, (lamTG M (i + 1) τ).detShift = -C.sDiv i τ := by
  first | exact @GlobalTheory.KerWtStep.trueWt_step | exact GlobalTheory.KerWtStep.trueWt_step | (intros; apply GlobalTheory.KerWtStep.trueWt_step <;> assumption)
