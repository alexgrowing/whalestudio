import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAllOnesProdOneAddMul
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_exL_dual : T_exL_dual := by
  intro n L m a
  exact GlobalTheory.coeff_allOnes_prod_one_add_mul (σ := EntIdx n) m a

end GlobalTheory.PsCo.Cw2a
