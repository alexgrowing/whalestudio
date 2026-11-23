import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualProdLogDerivModSq
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_dual_prod : T_dual_prod := by
  intro A _ _ D L la m J hD hsq
  exact GlobalTheory.dualProd_logDeriv_modSq (K := ℂ) D la m J hD hsq

end GlobalTheory.PsCo.Cw2a
