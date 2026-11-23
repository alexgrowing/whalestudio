import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MotiveBoundOfSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.motive_bound_of_series : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, MvB hL := by
  first | exact @GlobalTheory.HeightCounting.Up.mvB_of_classicalTheorems | exact GlobalTheory.HeightCounting.Up.mvB_of_classicalTheorems | (intros; apply GlobalTheory.HeightCounting.Up.mvB_of_classicalTheorems <;> assumption)
