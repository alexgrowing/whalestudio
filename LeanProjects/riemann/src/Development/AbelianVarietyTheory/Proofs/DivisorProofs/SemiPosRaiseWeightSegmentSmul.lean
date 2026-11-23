import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem semiPos_up_smul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (u : SmFn p)
    (t : ℝ), 0 ≤ t → t ≤ 1 → L.SemiPos D → (up L u).SemiPos D → (up L (u.smul t)).SemiPos D := by
  intro k _ X p D L u t h0 h1 hL hLu σ i c y hy ξ
  set f : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => (L.φ σ).φ i (c.e.symm v) with hfdef
  set g : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => u.u σ (c.e.symm v) with hgdef
  have hf : ContDiffAt ℝ 2 f (c.e y) := (L.cInf σ).contDiffAt c hy.1 hy.2
  have hfg : ContDiffAt ℝ 2 (fun v => f v + g v) (c.e y) := ((up L u).cInf σ).contDiffAt c hy.1 hy.2
  have a : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (f v : ℂ)) (c.e y) ξ).re := hL σ i c y hy ξ
  have b : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((f v + g v : ℝ) : ℂ)) (c.e y) ξ).re := hLu σ i c y hy ξ
  have e : (fun v => (((up L (u.smul t)).φ σ).φ i (c.e.symm v) : ℂ)) =
      fun v => ((((1 - t) * f v + 0) + (t * (f v + g v) + 0) : ℝ) : ℂ) := by
    funext v
    show ((((L.φ σ).φ i (c.e.symm v) + t * u.u σ (c.e.symm v)) : ℝ) : ℂ) = _
    congr 1
    simp only [hfdef, hgdef]
    ring
  rw [e, ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_add, ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hf,
    ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul (f := fun v => f v + g v) hfg]
  · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have : 0 ≤ 1 - t := by linarith
    positivity
  · exact (hf.const_smul (1 - t)).add contDiffAt_const
  · exact (hfg.const_smul t).add contDiffAt_const

end GlobalTheory.HSAmp
