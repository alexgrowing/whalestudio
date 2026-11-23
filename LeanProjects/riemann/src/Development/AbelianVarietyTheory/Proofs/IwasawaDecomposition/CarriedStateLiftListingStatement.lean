import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedStateLiftListing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carried_state_lift_listing : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ P x => ∀ D0 : D7, SeriesLevel hL x → Carried D0 (Dof x) → ∃ x' : St P, Nonempty (StrictHenselianAcyclic hL x') ∧ Carried D0 (Dof x') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x' := by
  first | exact @GlobalTheory.HeightCounting.Up.points_carried | exact GlobalTheory.HeightCounting.Up.points_carried | (intros; apply GlobalTheory.HeightCounting.Up.points_carried <;> assumption)
