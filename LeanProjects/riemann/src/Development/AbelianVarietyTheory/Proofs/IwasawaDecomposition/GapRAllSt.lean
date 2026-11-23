import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Up.GapAllStates

theorem gapR_allSt : AllSt fun _ _ _ _ _ _ x => ∀ (τ : (Dof x).what₂.Tau) (n : ℕ), n + 1 < (Dof x).R.r →
    100 * ((Dof x).R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt ((Dof x).hc τ) n - Formalism.L2.NTheta.lamAt ((Dof x).hc τ) (n + 1) :=
  Step.of_evG (EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
    fun _ _ _ _ _ hK _ _ _ hO _ _ _ w _ _ x => (hK (w.st x.o.Z) hO).1.gapR)

end GlobalTheory.HeightCounting.Up.GapAllStates
