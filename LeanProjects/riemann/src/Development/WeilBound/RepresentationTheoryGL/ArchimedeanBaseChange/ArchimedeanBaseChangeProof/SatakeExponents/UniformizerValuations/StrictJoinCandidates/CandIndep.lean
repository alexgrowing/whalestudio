import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CandSt

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

theorem candIndep : CandIndep := by
  intro hR E _ _ _ n π S F₀ T' c c' e e' b b' i s₁ s₂ Pa Pb D
  constructor
  · intro h
    exact ⟨h.ctx, h.leaves₁, h.leaves₂, h.inf₁, h.inf₂, h.vec⟩
  · intro h
    exact ⟨h.ctx, h.leaves₁, h.leaves₂, h.inf₁, h.inf₂, h.vec⟩

end PositivityTheory.Rg.BcB.F.FX

end
