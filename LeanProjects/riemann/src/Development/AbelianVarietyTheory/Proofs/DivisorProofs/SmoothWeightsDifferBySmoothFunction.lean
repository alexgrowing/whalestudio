import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem weight_sub_cInf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X) (φ ψ : Weight p σ B), φ.IsCInf → ψ.IsCInf → ∃ u : CxPts p σ → ℝ, (∀ y, CInfAt u y) ∧ ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y + u y := by
  intro k _ X p σ B φ ψ hφ hψ
  have key : ∀ i y, y ∈ ptsIn p σ (B.U i) →
      ψ.φ i y - φ.φ i y = ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y := by
    intro i y hi
    rw [ψ.trans _ i y (mem_pick φ.isLB y) hi, φ.trans _ i y (mem_pick φ.isLB y) hi]
    ring
  refine ⟨fun y => ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y, fun y => ?_, fun i y hi => ?_⟩
  · have hy := mem_pick φ.isLB y
    have hs : CInfAt (fun z => ψ.φ (pick φ.isLB y) z + -φ.φ (pick φ.isLB y) z) y :=
      (hψ _ y hy).add (hφ _ y hy).neg
    refine hs.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hy] with z hz
    rw [← key _ z hz, sub_eq_add_neg]
  · have := key i y hi
    linarith

end GlobalTheory.Mix
