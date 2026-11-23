import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAllOnesSumAlgEquivMkDerivationStatement

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem exL_dL_holds : GlobalTheory.PsCo.Cw2a.T_exL_dL := by
  intro n L ε x b
  have h := GlobalTheory.T.coeff_allOnes_sumAlgEquiv_derivation_eq (σ := EntIdx n) (L := L) (dM ε x) b
  simpa [exL, dL, inL, allOnes] using h

end GlobalTheory.PsCo.Cw2a
