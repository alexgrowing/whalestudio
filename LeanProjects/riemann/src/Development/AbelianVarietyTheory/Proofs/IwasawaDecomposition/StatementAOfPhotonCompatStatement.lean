import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StatementAOfPointCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.statement_a_of_point_compat : PrN → PhtCmp → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SAk hL := by
  first | exact @GlobalTheory.HeightCounting.Up.sak_of_prN | exact GlobalTheory.HeightCounting.Up.sak_of_prN | (intros; apply GlobalTheory.HeightCounting.Up.sak_of_prN <;> assumption)
