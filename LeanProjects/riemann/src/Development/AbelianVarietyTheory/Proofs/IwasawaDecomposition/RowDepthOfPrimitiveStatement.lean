import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowDepthOfPrimitive
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_depth_of_primitive : PrN → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  first | exact @GlobalTheory.RowDepthTrue.rowDepth_allSt | exact GlobalTheory.RowDepthTrue.rowDepth_allSt | (intros; apply GlobalTheory.RowDepthTrue.rowDepth_allSt <;> assumption)
