import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenOccurrenceWithLocalData
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMemAnd
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
theorem _root_.GlobalTheory.T.eigen_occurrence_with_local_data : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ Sb : Finset (PlE c.a.nt.D.host), (∀ i, Sb ⊆ (withLoc c.a.nt.L).ntw.S0 i) ∧ (∀ Rw : RowSide (withLoc c.a.nt.L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (withLoc c.a.nt.L) (cfL c.a.nt.L c.a.nt.cf) Rw Sb c.a.nt.eig) ∧ GlobalTheory.TwInputs.EigOcc (withLoc c.a.nt.L) ({ c.a.nt.S with } : RatDat (withLoc c.a.nt.L).ntw) c.a.nt.θ c.a.nt.hL Sb c.a.nt.eig := by
  first | exact @GlobalTheory.GalLoc.EigLoc.eig_at | exact GlobalTheory.GalLoc.EigLoc.eig_at | (intros; apply GlobalTheory.GalLoc.EigLoc.eig_at <;> assumption)
