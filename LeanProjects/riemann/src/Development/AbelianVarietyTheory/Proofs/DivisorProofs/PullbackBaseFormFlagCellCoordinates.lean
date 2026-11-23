import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordinatesContDiffAtEtaleChartStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpression
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VarietyComplexPointsMapIsHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompLinearStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pullback_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (α : (atlas X σ).Fld), (atlas X σ).IsForm α → ∀ x : (atlas Y σ).Pt, x.pt ∈ cellSet E E' φ f hf c A u → (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α x = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (pull (bsL ε) ((atlas X σ).loc α c (bsL ε (cellMap ε f hf c u x.pt)))) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u n ε α hα x hx
  have hs : ptMap σ f hf x.pt ∈ ((atlas X σ).e c).source := hx.2
  rw [GlobalTheory.CxForm.pullback_eq_chart _ _ _ _ (atlas X σ) (atlas Y σ) (ptMap σ f hf) α (GlobalTheory.T.varietyComplexPointsMap_isHolomorphic F σ X Y f hf) hα x c hs]
  have hb : bsL ε (cellMap ε f hf c u x.pt) = c.e (ptMap σ f hf x.pt) := bsL_pt _ _ _
  have hloc : (atlas X σ).loc α c (c.e (ptMap σ f hf x.pt)) = α ⟨(c, ptMap σ f hf x.pt), hs⟩ :=
    (atlas X σ).loc_crd α ⟨(c, ptMap σ f hf x.pt), hs⟩
  rw [hb, hloc, ← GlobalTheory.T.pullbackComplexFormsLinearMap_comp_linear]
  congr 1
  have he : (atlas X σ).e c ∘ ptMap σ f hf ∘ x.ch.symm = bsL ε ∘ (cellMap ε f hf c u ∘ x.ch.symm) := by
    funext w
    simp only [Function.comp_apply, cellMap, bsL_pt]
    rfl
  have hd : DifferentiableAt ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd :=
    (GlobalTheory.T.flagCellCoordinates_contDiffAt_etaleChart F σ X Y ι m E E' φ f hf hR c A u n ε x hx).differentiableAt (by norm_num)
  rw [he, fderiv_comp x.crd (bsL ε).differentiableAt hd, ContinuousLinearMap.fderiv]

end GlobalTheory.FlagCell2
