import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.DerivSub
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHoldsStatement

namespace GlobalTheory.RgGu.Nup2

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.NuPair k := fun k _ _ _ _ =>
  GlobalTheory.T.nu_pair_of_derivatives_jacquet k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    (GlobalTheory.T.derivative_jacquet_holds k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)
    (GlobalTheory.T.jm_theta_holds k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)
    (derivSub_main k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top)

end GlobalTheory.RgGu.Nup2
