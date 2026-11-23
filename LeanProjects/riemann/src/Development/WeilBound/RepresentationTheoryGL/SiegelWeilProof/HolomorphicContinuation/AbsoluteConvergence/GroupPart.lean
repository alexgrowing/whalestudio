import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.WeightFactorDilation
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DenseCell

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

theorem groupPart : GroupPart := by
  intro n X a ha
  exact ⟨dil_mul ha, dil_zero ha, dil_up ha, cont_dil ha, fun y hy s => up_mul hy (dil_up ha s), cell_dec,
    fun g b hg h => conj_cell ha g b hg h, fun y hy s => cell_mul ha y hy s, dense_cell,
    fun p q e h => weight_factor_dilation ha p q e h⟩

end PositivityTheory.Rg.Sw.AbsSt.DF
