import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.ChartShrink

theorem exists_chart_le : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (σ : k →+* ℂ) (c₀ : AlgChart q σ 1) (y : CxPts q σ), y ∈ c₀.e.source → ∀ V : B.Opens, y ∈ ptsIn q σ V → ∃ c : AlgChart q σ 1, y ∈ c.e.source ∧ c.U ≤ V := by
  intro k _ B q σ c₀ y hy V hV
  have hy0 : y ∈ ptsIn q σ c₀.U := c₀.source_subset hy
  obtain ⟨f, hfV, hf⟩ := c₀.affine.exists_basicOpen_le (V := V) ⟨_, mem_ptsIn.1 hV⟩ (mem_ptsIn.1 hy0)
  have hle : B.basicOpen f ≤ c₀.U := B.basicOpen_le f
  have hE : (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q (B.basicOpen f))
      (fun a => resG B hle (c₀.x a))).Etale := by
    have e : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q (B.basicOpen f))
        (fun a => resG B hle (c₀.x a)) =
        (resG B hle).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q c₀.U) c₀.x) := by
      rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
    rw [e]
    have hR : (resG B hle).Etale := by
      letI : Algebra Γ(B, c₀.U) Γ(B, B.basicOpen f) := (resG B hle).toAlgebra
      haveI : IsLocalization.Away f Γ(B, B.basicOpen f) := c₀.affine.isLocalization_basicOpen f
      exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
    exact RingHom.Etale.stableUnderComposition _ _ c₀.etale hR
  obtain ⟨c, hc, hU, -⟩ := AlgChart.exists_of_etale (c₀.affine.basicOpen f) _ hE (mem_ptsIn.2 hf)
  exact ⟨c, hc, hU ▸ hfV⟩

end GlobalTheory.ChartShrink
