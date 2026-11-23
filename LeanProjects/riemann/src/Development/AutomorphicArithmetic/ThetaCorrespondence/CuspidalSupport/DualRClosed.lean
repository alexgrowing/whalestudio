import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.DualROfCbcc
import Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc

namespace UpperTheory.Lit.Car

theorem dualR_closed (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hP : GlobalTheory.Published.GaloisRepOfPolarizedPair) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : DualR :=
  dualR_of_cbcc UpperTheory.ConvolutionTheory.cbcc hF hGK hP hB hL hJ

end UpperTheory.Lit.Car
