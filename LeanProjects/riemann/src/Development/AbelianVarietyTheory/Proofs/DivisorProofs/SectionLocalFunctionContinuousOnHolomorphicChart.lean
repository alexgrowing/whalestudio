import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem loc_continuousOn_holo : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField), f ∈ P.H a b → ∀ i j, ContinuousOn (ratVal (q := p) (σ := σ) (P.loc a b f i j)) (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) ∧ ∀ (D : ℕ) (c : AlgChart p σ D), DifferentiableOn ℂ (fun v => ratVal (P.loc a b f i j) (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j))) := by
  intro k _ X _ p P a b σ f hf i j
  have key : ∀ y ∈ ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j), ∃ (W : X.Opens) (hW : genericPoint X ∈ W)
      (g : Γ(X, W)), y ∈ ptsIn p σ W ∧ P.loc a b f i j = fnOf W hW g := by
    intro y hy
    have hr : RegAt (under y) (P.loc a b f i j) := hf _ i j (mem_ptsIn.1 hy.1) (mem_ptsIn.1 hy.2)
    obtain ⟨W, hx, g, e⟩ := hr.exists_fnOf
    exact ⟨W, gen_mem hx, g, mem_ptsIn.2 hx, e.symm⟩
  refine ⟨fun y hy => ?_, fun D c => ?_⟩
  · obtain ⟨W, hW, g, hy', e⟩ := key y hy
    have hc : ContinuousAt (ratVal (q := p) (σ := σ) (P.loc a b f i j)) y := by
      refine ((continuousOn_ev (p := p) (σ := σ) g).continuousAt ((isOpen_ptsIn W).mem_nhds hy')).congr ?_
      filter_upwards [(isOpen_ptsIn W).mem_nhds hy'] with z hz
      rw [e, ratVal_fnOf hz]
    exact hc.continuousWithinAt
  · intro v hv
    obtain ⟨W, hW, g, hy', e⟩ := key _ hv.2
    have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ W) :=
      c.e.isOpen_inter_preimage_symm (isOpen_ptsIn W)
    have hm : v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ W := ⟨hv.1, hy'⟩
    have hd := (c.holo W g).differentiableAt (hO.mem_nhds hm)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hO.mem_nhds hm] with w hw
    rw [e, ratVal_fnOf hw.2]
    rfl

end GlobalTheory.HSAmp
