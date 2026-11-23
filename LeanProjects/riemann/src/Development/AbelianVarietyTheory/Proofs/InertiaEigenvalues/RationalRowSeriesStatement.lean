import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalRowSeries
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_row_series : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => ∀ (l : StrictHenselianAcyclic hL x) (i : (Dof x).ntw.Tw), (Dof x).ntw.NonzeroIndexPlace i → ∀ j b, GlobalTheory.SeriesTie.RatRow l.b.YS x.m.z.geo.v₀ l.b.ser.ex.good i j b := by
  first | exact @GlobalTheory.PlaceRead.SeriesAtState.ratRow_at_state | exact GlobalTheory.PlaceRead.SeriesAtState.ratRow_at_state | (intros; apply GlobalTheory.PlaceRead.SeriesAtState.ratRow_at_state <;> assumption)
