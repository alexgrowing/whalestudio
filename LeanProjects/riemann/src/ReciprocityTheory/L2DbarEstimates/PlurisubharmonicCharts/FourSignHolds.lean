import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.HyPhi
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxL
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AExact
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeLoc
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeD
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ImportsAlt
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZeroDimA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GrowSumIndicatorLe
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourIndep
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourBasic

namespace ReciprocityTheory.L2DbarEstimates.Y

section
variable (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La]

end

theorem four_sign_holds (f : ℕ) : FOURSignStatement f :=
  four_sign f (four_indep f) (four_bound f)

end ReciprocityTheory.L2DbarEstimates.Y
