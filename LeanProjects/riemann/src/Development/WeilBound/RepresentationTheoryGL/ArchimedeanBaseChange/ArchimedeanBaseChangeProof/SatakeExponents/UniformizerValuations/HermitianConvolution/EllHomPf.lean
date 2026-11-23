import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.NontrivInf

noncomputable section

open MeasureTheory
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FBL

theorem ellHom_holds : EllHom := by
  intro E _ _ _ a b _ _ μ₁ μ₂ c φ
  unfold ellSum2
  rw [mul_finsum]
  refine finsum_congr fun q => ?_
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs with hP
  swap
  · simp
  unfold orbTerm2 PositivityTheory.Rg.Tf.Loc.quotIntegral
  split_ifs with hρ
  · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  · simp

end PositivityTheory.Rg.BcB.F.FBL

end
