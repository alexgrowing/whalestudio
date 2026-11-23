import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBoundOfPrimitive
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_bound_of_primitive : (PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ cDep : ℝ, SeriesExistList hL cDep) := by
  first | exact @GlobalTheory.HeightCounting.Up.SeriesStep.sb1l | exact GlobalTheory.HeightCounting.Up.SeriesStep.sb1l | (intros; apply GlobalTheory.HeightCounting.Up.SeriesStep.sb1l <;> assumption)
