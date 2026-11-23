import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeImageComplPtsIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarChartMeasureTransfer
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2Null

theorem part_compl_ptsIn : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : Var F) (β : (atlas Y σ).Fld) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ s : ℤˣ, (atlas Y σ).part β s (ptsIn Y.str σ W)ᶜ = 0 := by
  intro F _ σ Y β W hW s
  exact GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl fun c =>
    GlobalTheory.Mean4O.CoverInt.volume_image_compl_ptsIn F Y.X Y.str σ σ.injective
      (fun W hW => (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str W).injective) W hW _ c

end GlobalTheory.FlagCell2Null
