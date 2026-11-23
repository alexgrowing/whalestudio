import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU

namespace Formalism.L2.Th1.F

theorem curveBridge_of (hw : Formalism.L2.Th1.A.BridgeWp) (hu : IsWpUnique) (ht : TaylorIsWp) : CurveBridge := by
  intro W L h2 h3
  have h := hw ℂ W
  rw [h2, h3] at h
  exact hu ℂ L.g₂ L.g₃ _ _ h (ht L)

theorem curve_weierstrass_series_eq : CurveBridge :=
  curveBridge_of Formalism.L2.Th1.A.bridgeWp weierstrass_series_unique (taylorIsWp_of taylor_ring taylor_deriv)

end Formalism.L2.Th1.F
