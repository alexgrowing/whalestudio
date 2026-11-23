import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem LatticesAgree.equiv :
    GroundTheory.Heights₂.Heights.Model.LatticesAgree.Statement ↔ LatticesAgree.Statement := by
  constructor
  · intro h A K V _ _ _ _ _ _ _ _ _ _ _ _ M N hMf hMp hNf hNp hMs hNs hloc
    refine h A K V M N hMf hMp hNf hNp hMs hNs fun p hp => ?_
    exact SetLike.coe_injective (hloc p.asIdeal p.isPrime hp)
  · intro h A _ _ _ _ K _ _ _ V _ _ _ _ _ M N hMf hMp hNf hNp hMs hNs hloc
    refine h A K V M N hMf hMp hNf hNp hMs hNs fun p hp hh => ?_
    have e := hloc ⟨p, hp⟩ hh
    exact congrArg (fun P : Submodule A V => (P : Set V)) e

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
