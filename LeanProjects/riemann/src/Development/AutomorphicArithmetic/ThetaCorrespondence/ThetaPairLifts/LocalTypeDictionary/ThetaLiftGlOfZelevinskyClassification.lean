import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.MingZel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGeneralLinearStatement

section
open MeasureTheory GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel PositivityTheory.Tls2.Ming3 PositivityTheory.Rg.Ming
open scoped TensorProduct
namespace UpperTheory.Lit.HoweDuality
theorem thetaLift_gl_of_zelevinsky_classification (hZ : ZelevinskyPolynomialRing) : _root_.GlobalTheory.ThetaLiftGL.ThetaLiftGeneralLinearStatement :=
  fun hBZ _ k _ _ _ _ r t μ V _ _ W _ _ σ π hrt hμs hμu hσs hσi hσu hπs hπi hθ =>
    lift_of_irr k r t μ V W σ π hrt hμs hμu hσu hπs hπi
      (UpperTheory.Lit.Mix.top (GlobalTheory.geometricLemma_of_filtration hBZ GlobalTheory.geometricLemmaFiltration_unconditional) hBZ hZ
        k r t V σ μ hrt hσs hσi hσu hμs hμu) hθ
end UpperTheory.Lit.HoweDuality
end
