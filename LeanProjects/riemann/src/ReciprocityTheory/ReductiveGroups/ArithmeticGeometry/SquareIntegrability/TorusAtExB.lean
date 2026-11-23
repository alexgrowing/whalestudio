import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceIntegralBasis

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate

noncomputable section

namespace TX

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Ef (u v : Fin r → E) : ℚ := Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v)

theorem flagDomainConj_hostXi_eq_neg : cc X.ξ0 = -X.ξ0 := X.ξ0_im

end TX

end

end ReciprocityTheory.ChartRestriction.G.I2
