import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGreenCuspidalLabellingSameGenerators
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
theorem _root_.GlobalTheory.T.exists_green_cuspidal_labelling_same_generators : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7) (cf : CharFrame D) (Γ : GrpSide D), TypesTrue D.ntypes cf.P cf.W → (∀ k, Γ.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩)) → ∃ Γ' : GrpSide D, GlobalTheory.PendOf.GreenLab Γ' ∧ ∀ k, Γ'.ζ k = Γ.ζ k := by
  first | exact @GlobalTheory.GreenSide.exists_greenLab | exact GlobalTheory.GreenSide.exists_greenLab | (intros; apply GlobalTheory.GreenSide.exists_greenLab <;> assumption)
