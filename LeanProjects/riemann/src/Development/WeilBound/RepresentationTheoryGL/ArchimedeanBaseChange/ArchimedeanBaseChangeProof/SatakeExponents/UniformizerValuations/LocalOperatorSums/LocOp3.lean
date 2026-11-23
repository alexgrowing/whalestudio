import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMulSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermConvolutionHecke
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexEqCard

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcN.F2.LocOpPf

theorem locOp3 (E : Type) [Field E] [NumberField E] [IsCMField E] : LocOpUniformizer E := by
  intro n a b h w K' hK'o hK'le hK'n X hXK hX
  exact ⟨GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.constant_term_locally_constant E n a b h w K' hK'o hK'le hK'n X hXK hX, GlobalTheory.CompanionTheory.DiagAvg.ct_eq_diag E n a b h w K' hK'o hK'le hK'n X hXK hX,
    GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution E n a b h w K' hK'o hK'le hK'n X hXK hX, GlobalTheory.CompanionTheory.HeckeAct.hk_ind_apply E n a b h w K' hK'o hK'le hK'n X hXK hX⟩

end PositivityTheory.Rg.BcN.F2.LocOpPf
