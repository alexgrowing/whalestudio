import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowLocalAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_local_all : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, ParIn hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ σ, RowLoc (w.st Z).toD7 Rw σ := by
  first | exact @GlobalTheory.RowSphSmall.rowLoc_overRows | exact GlobalTheory.RowSphSmall.rowLoc_overRows | (intros; apply GlobalTheory.RowSphSmall.rowLoc_overRows <;> assumption)
