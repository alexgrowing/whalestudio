import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

theorem AdmProd_holds : AdmProd := by
  intro E _ _ _ n P w K hKo hKle
  have hadm := GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr (w.adicCompletion E) P.N P.h (fun i => P.σ i w)
  have hKc : IsCompact (K : Set (GLw n w)) :=
    (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w n).of_isClosed_subset (K.isClosed_of_isOpen hKo) hKle
  exact hadm.2 K hKo hKc

end PositivityTheory.Rg.BcB.F.FX.Bo

end
