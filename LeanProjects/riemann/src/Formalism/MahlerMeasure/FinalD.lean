import Formalism.MahlerMeasure.MahlerMeasureProofs.GaussRad
import Formalism.MahlerMeasure.MahlerMeasureProofs.MahlerK
import Formalism.MahlerMeasure.MahlerMeasureProofs.SmithZp
import Formalism.MahlerMeasure.MahlerMeasureProofs.LieMat
import Formalism.MahlerMeasure.MahlerMeasureProofs.LieRoots
import Formalism.MahlerMeasure.MahlerMeasureProofs.DeterminantBlockLeadingTerm
import Formalism.MahlerMeasure.MahlerMeasureProofs.SmithBall

namespace Formalism.GM.Top
open Formalism.GM
theorem smithZp : SmithZp := smith_form_p_adic_integers
theorem lieMat : LieMat := lieMat_of mahler_binomial_unit_ball
theorem lieRoots : LieRoots := lieRoots_of gauss_norm_multiplicative
theorem valuation_window_lower_bound : ValuationWindowLowerBound := by
  intro p _ K _ _ _ n del₀ h E c lead roots t₀ U V d hc hU hV hUd hVd hE hdel hlead hdet hsm
  exact lieRoots p K h _ E _ lead roots t₀ hE hlead hdet
    (lieMat p K n del₀ h E c t₀ U V d hc hU hV hUd hVd hE hdel hsm)
end Formalism.GM.Top
