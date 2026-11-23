import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompatibleOfSameSplittingCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftConstantTermCompatibleWeilStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerConstTermObj

theorem towerConstTerm : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D := by

  intro D V V' W r C B hsplit ψ χS χT χT' ω ω' hω hω'
  have hcomp : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.Compatible ψ V V' W C B ω ω' :=
    GlobalTheory.T.weilCompatible_of_sameSplittingCharacter D V V' W r C B hsplit ψ χS χT χT' ω ω' hω hω'
  exact GlobalTheory.T.thetaLift_constantTerm_compatibleWeil D V V' W r C B hsplit ψ χS χT χS χT' ω ω' hω hω' hcomp

end GlobalTheory.TowerConstTermObj
