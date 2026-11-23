import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleAndLamUsedAllStates
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_and_lam_used_all_states : PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ _ _ _ x => SumRepresentations.adm8 (Dof x) ∧ GlobalTheory.NRows.LamUsed (Dof x) := by
  first | exact @GlobalTheory.HeightCounting.Up.RowsAtStates.parts_lam_allSt | exact GlobalTheory.HeightCounting.Up.RowsAtStates.parts_lam_allSt | (intros; apply GlobalTheory.HeightCounting.Up.RowsAtStates.parts_lam_allSt <;> assumption)
