import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaBarEnum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.DVR

theorem cmLiftCondition_of_dimSplit (hL : ReciprocityTheory.ChartRestriction.G.Out.Laws) (h1c : PositiveValuationMaximalIdeal) (h2f : DvrLevelFrame)
    (h3 : FiniteOrderValuationInvariance) (hU : UUStatement) (hC : CanonLiftFixStatement) (hdim : DimSplitStatement) :
    OneCStatement :=
  oneC_of hL (phiFun_of_globalFns hL.globalFns) h1c
    (pullback_valuation_forward_of (pullGen_of hL.globalFns) (QuadraticAlgebraValuation.qAl_of hL)) h2f h3 hU (finOrdExists_of_laws hL)
    (alphaBarEnum_holds hL.weil hL.mulN) hC alphaPair_holds hdim

theorem cmLiftCondition_of_torsion (hL : ReciprocityTheory.ChartRestriction.G.Out.Laws) (h1c : PositiveValuationMaximalIdeal) (hTW : TWStatement)
    (hU : UUStatement) (hC : CanonLiftFixStatement) (hdim : DimSplitStatement) : OneCStatement :=
  cmLiftCondition_of_dimSplit hL h1c (levelFrame_of_laws hL) (galois_fixed_adelic_matrices_descend hL hTW) hU hC hdim

end ReciprocityTheory.ChartRestriction.G.H1
