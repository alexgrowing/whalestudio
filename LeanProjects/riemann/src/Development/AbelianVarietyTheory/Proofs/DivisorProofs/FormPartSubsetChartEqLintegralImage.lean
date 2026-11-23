import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlagCell2

theorem part_subset_chart : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (s : ℤˣ) (i : A.ι) (T : Set M), MeasurableSet T → T ⊆ (A.e i).source → A.part β s T = ∫⁻ v in A.e i '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β i v)).re) := by
  intro M _ _ _ _ _ n A β hβ s i T hT hTi
  set ρ : A.ι → M → ENNReal := fun k y => ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β k (A.e k y))).re) with hρ
  have hp : A.part β s = ChartGlue.glueMeas A.e ρ := rfl
  have hρc : ∀ k l y, y ∈ (A.e k).source → y ∈ (A.e l).source →
      ρ k y = ENNReal.ofReal (‖ChartGlue.transDet (A.e k) (A.e l) y‖ ^ 2) * ρ l y := by
    intro k l y hk hl
    have h1 := A.loc_crd β (⟨(k, y), hk⟩ : A.Pt)
    have h2 := A.loc_crd β (⟨(l, y), hl⟩ : A.Pt)
    have h3 := hβ.compat (⟨(k, y), hk⟩ : A.Pt) ⟨(l, y), hl⟩ rfl
    simp only [hρ]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ChartGlue.transDet]
    ring
  rw [hp, ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hT hTi, ChartGlue.chartMeas_apply_of_subset _ _ hT hTi]
  refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hT hTi) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [hρ, (A.e i).left_inv (hTi hy)]

end GlobalTheory.FlagCell2
