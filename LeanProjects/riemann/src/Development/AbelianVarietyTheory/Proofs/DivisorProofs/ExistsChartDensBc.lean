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

set_option autoImplicit false

namespace GlobalTheory.Mix

theorem exists_chart_dens_bc : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ) (D : ℕ) (c : AlgChart p (τ.comp ρ) D) (z : CxPts q τ), bcPt hp.w τ z ∈ c.e.source → ∃ c' : AlgChart q τ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, bcPt hp.w τ w ∈ c.e.source ∧ c'.e w = c.e (bcPt hp.w τ w) ∧ ∀ L : Fin D → MLine p (τ.comp ρ), dens (fun i => (L i).bc hp.w τ) c' w = dens L c (bcPt hp.w τ w) := by
  intro k K _ _ ρ X G p q j hp τ D c z hz
  have hm : ∀ w, (bcPt hp.w τ w).1 = w.1 ≫ j := fun _ => rfl
  obtain ⟨c₀, hz₀, h, hx⟩ := c.exists_baseChange hp hm hz
  let c' := c₀.restr (bcPt hp.w τ ⁻¹' c.e.source) (c.e.open_source.preimage (continuous_bcPt hp.w τ))
  have H : ∀ w ∈ c'.e.source, bcPt hp.w τ w ∈ c.e.source ∧ c'.e w = c.e (bcPt hp.w τ w) := by
    intro w hw
    rw [AlgChart.restr_source] at hw
    refine ⟨hw.2, ?_⟩
    change c₀.e w = _
    ext a
    rw [c.apply_eq _ hw.2, c₀.apply_eq _ hw.1, hx, ev_appLE_of_comp hm h _ (c₀.source_subset hw.1)]
  refine ⟨c', by rw [AlgChart.restr_source]; exact ⟨hz₀, hz⟩, fun w hw => ⟨(H w hw).1, (H w hw).2, fun L => ?_⟩⟩
  have hw' := (H w hw).1
  have key (N : MLine p (τ.comp ρ)) :
      c'.hess (N.bc hp.w τ).φ (pick (N.bc hp.w τ).φ.isLB w) w =
        c.hess N.φ (pick N.φ.isLB (bcPt hp.w τ w)) (bcPt hp.w τ w) := by
    have hj := mem_of_mem_linComb (m := fun _ => bcPt hp.w τ w) (fun _ => rfl)
      (mem_pick (N.bc hp.w τ).φ.isLB w) PUnit.unit
    rw [c.hess_eq N.cInf hw' hj (mem_pick _ _), AlgChart.hess,
      AlgChart.hess, ← (H w hw).2, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr]
    filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hw)] with v hv
    obtain ⟨h₁, h₂⟩ := H _ (c'.e.map_target hv)
    rw [c'.e.right_inv hv] at h₂
    have e₁ : c.e.symm v = bcPt hp.w τ (c'.e.symm v) := (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
    rw [e₁]
    simp [MLine.bc, Weight.linComb]
  simp only [dens, key]

end GlobalTheory.Mix
