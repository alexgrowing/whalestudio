import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapAdInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfCVUnderIntOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichRhoAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll

theorem Formalism.FourierDecayAlt.P.capelli_det_ad_invariant : Formalism.FourierDecayAlt.P.JFxB.CapAdInv := by
  exact Formalism.FourierDecayAlt.P.JFxE.capAdInv

theorem Formalism.FourierDecayAlt.P.capelli_right_invariant : Formalism.FourierDecayAlt.JF.CVRight := by
  exact Formalism.FourierDecayAlt.P.JFxE.cVRight

theorem Formalism.FourierDecayAlt.P.capelli_rho_commute : Formalism.FourierDecayAlt.JF.CVRho := by
  exact Formalism.FourierDecayAlt.P.JFxE.cVRho

theorem Formalism.FourierDecayAlt.P.jf_cVUnderInt_of_jDom : Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.JF.CVUnderInt := by
  intro hD
  exact Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of (Formalism.FourierDecayAlt.P.bessel_words_of_domain hD) Formalism.FourierDecayAlt.P.JFxB.cvWordSum
    Formalism.FourierDecayAlt.P.rewrite_rho_action
