import Formalism.HermitianCurvature.TopDensNonnegOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HerClassesOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopDensNonnegOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfWaveQQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvSelf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem herClassesOfPartsD : HerClassesOfPartsD := by
  intro hNF hKP hZS hAn Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' _ _
  obtain ⟨hAdj, hSD, hFI, hCor⟩ := hAn Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  have hXK := xKappaOfNF hNF hKP Wp Wq P z z' π π' X μ L st l0 hD
  have hTD := topDensNonnegOfKappa Wp Wq S P z z' π π' X μ L st l0 (herK S P z z' π π' L st l0 D) hD hl1 hl2 hXK
  have hTT := topTwistDensOfZeta hZS Wp Wq S P z z' π π' X μ L st l0 (herK S P z z' π π' L st l0 D) hD
  have hFS := formSesqOfInt Wp Wq S P z z' π π' μ L st l0 _ hFI
  refine ⟨herK S P z z' π π' L st l0 D, hAdj, hTD, ?_, herK_sliceIn, hSD, herK_waveK, hFS, hCor, ?_⟩
  · intro w hw s Wv Wv' hW hW' x y hx hy c hc
    exact ⟨herK_waveZ w hw s Wv Wv' hW hW' x hx, hTT w hw s Wv Wv' hW hW' x y hx hy c hc⟩
  · intro F ε hε hF hG
    obtain ⟨Φ, hΦ⟩ := radJFExists Wp Wq P z z' π π' D F hD.1 hz hz' hπ hπ' ⟨hF, ε, hε, hG⟩
    exact ⟨Φ, herK_jf F ⟨hF, ε, hε, hG⟩ Φ hΦ, hΦ⟩

theorem thmPActualOfNFZ (hNF : NormalFormActual) (hZS : NF.ActualZetaSmooth) (hAn : HerAnalyticCAll) : ThmPActual :=
  thmPActualFromHer (herClassesOfPartsD hNF kappaFibrePos hZS hAn) waveCommQQAll

theorem thmPActualOfZ (hZS : NF.ActualZetaSmooth) (hAn : HerAnalyticCAll) : ThmPActual :=
  thmPActualOfNFZ Formalism.FourierDecayAlt.P.normal_form_actual hZS hAn

end Formalism.FourierDecayAlt.P5
