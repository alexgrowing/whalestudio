import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.KUEqKLOfNotMemBad
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Mok0
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.MapSplit
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.HkConstMul
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.MuVal
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEig
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IsHeckeFsum
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.SatCompAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.ExTbOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.InertInSecAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CandIndep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.FrameInertAll
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertEigenvalues.EigInert
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.BcWeyl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.SumPairSignEqRho
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PTarget
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebraStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpectralTraceOfModelAlgebraStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryModelHoldsStatement

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.FX
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

theorem gcHecke : GcHecke := by
  intro E _ _ _ n w hw b ϖ c
  have hg : gc w b ϖ c = ∑ x ∈ c.support,
      (c x * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)) • fU n w b ϖ (lOf x) := by
    funext γ
    simp only [gc, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hg]
  exact isHecke_fsum _ _ _ _ fun x => GlobalTheory.CompanionTheory.MatchPow.fU_hecke hw b ϖ _ (GlobalTheory.LocFinU.continuous_cj w)

theorem frameEx_of_fin (hUS : USide) (hCF : CandFin) : FrameEx :=
  frameEx_of hUS (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.CompanionTheory.LocHecke.locAlg) (GlobalTheory.T.spectral_trace_of_model_algebra GlobalTheory.T.unitary_model_holds GlobalTheory.CompanionTheory.LocHecke.locAlg)
    GlobalTheory.CompanionTheory.LocHecke.locAlg (exTbOf Inert.frameInert_all.1 Inert.frameInert_all.2.1 inertInSec) Inert.frameInert_all.2.2.2.1
    Inert.frameInert_all.2.2.2.2.1 (coneEigOf eigInert LemB.bcWeyl) satCompAt candIndep hCF
    (fun _ _ _ _ _ _ _ _ _ _ F₀ => mok0 F₀) IndefiniteRowSideFullHecke.coneTwo' gcHecke
    (locC IndefiniteRowSideFullHecke.shufEx' IndefiniteRowSideFullHecke.vResStd' IndefiniteRowSideFullHecke.shufStd' targetAlg monoRes) locE muVal powEig

end UpperTheory.HeckeLevelFrameExistence

end
