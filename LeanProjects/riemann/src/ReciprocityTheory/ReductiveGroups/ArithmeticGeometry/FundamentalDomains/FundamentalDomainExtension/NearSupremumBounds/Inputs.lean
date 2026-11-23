import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.NearSupremumBounds.FdFjNearSupOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow

namespace PI.FdFjNearSup.W

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem fourierJacobi_holomorphic : FjHolo (E := E) := by
  intro r X la P ξ ν hP hξ
  exact ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_diffOn X la P hP.1 hξ ν

theorem fourierJacobi_realFlow : FjRealFlow (E := E) := by
  intro r X la P ξ ν hP hξ x hx s
  have hP' : X.IsBddSec la P ∧ ∀ ξ', X.IsIso ξ' → ∀ y ∈ X.dom, X.fj la ξ' 0 P y = 0 := hP

  exact X.fj_flow_real la ξ hξ ν P hP'.1.1 hP'.1.2 x hx s

theorem fd_fj_near_sup_full :
    HolomorphicPeriodicityExtension (E := E) → FlowNormRatio (E := E) → ModerateCoefficientPositivity (E := E) →
      NearSupremumTransference (E := E) :=
  fd_fj_near_sup_of flowDomainCriterion_holds fourierJacobi_holomorphic fourierJacobi_realFlow orthonormalFlagTranslate_holds

end PI.FdFjNearSup.W
