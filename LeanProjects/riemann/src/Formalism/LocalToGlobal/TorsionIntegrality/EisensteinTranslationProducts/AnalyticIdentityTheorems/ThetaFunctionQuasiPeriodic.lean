import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroTranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassPSecondDerivative

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace SemicharacterPairingLemmas

open OperatorUThetaLemmas

lemma succ_mul_succ_sub_one_div_succ (m k a b : ℂ) (hm : m ≠ 0) : (m * (k * a)) / (m * b) = k * (a / b) := by
  rw [mul_div_mul_left _ _ hm, mul_div_assoc]

lemma altE_add_left (L : PeriodPair) (x y w : ℂ) : altE L (x + y) w = altE L x w + altE L y w := by
  rw [altE, altE, altE, herm_add_left, Complex.add_im]

lemma altE_self (L : PeriodPair) (x : ℂ) : altE L x x = 0 := by
  have h := altE_swap L x x
  linarith

end SemicharacterPairingLemmas

open SemicharacterPairingLemmas OperatorUThetaLemmas

theorem operator_u_theta : OpUTh0 := by
  intro L t x z
  rw [← opUMul L x t (sgStar L) z]
  simp only [th0, opU]
  ring

end Formalism.L2.Th1.F
