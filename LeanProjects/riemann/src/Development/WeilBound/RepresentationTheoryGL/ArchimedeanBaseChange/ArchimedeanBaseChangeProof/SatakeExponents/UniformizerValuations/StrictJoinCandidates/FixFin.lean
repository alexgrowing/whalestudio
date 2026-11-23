import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.FrameExOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotientsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProductsStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

theorem fixFin : FixFin := by
  intro E _ _ _ n D w K hKo hKc
  have hs : IsSmooth (Tail.prodAt D w) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hfl : HasFiniteLength (Tail.prodAt D w) :=
    GlobalTheory.T.finite_length_of_products (w.adicCompletion E) (Fin n) (Fin D.c) (fun i => Fin (D.N i)) (GlobalTheory.SmGL.stdBlocks D.N D.h)
      (fun i => (D.σ i w).V) (fun i => (D.σ i w).ρ) (fun i => (D.σ i w).smooth) (fun i => (D.σ i w).irred)
  have hadm : IsAdmissible (Tail.prodAt D w) :=
    GlobalTheory.T.admissible_of_finite_length_subquotients (Tail.prodAt D w) hs hfl fun W _ _ σ hsub hirr =>
      PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (w.adicCompletion E) n W σ (hsub.isSmooth hs) hirr
  exact hadm.2 K hKo hKc

end PositivityTheory.Rg.BcB.F.FX

end
