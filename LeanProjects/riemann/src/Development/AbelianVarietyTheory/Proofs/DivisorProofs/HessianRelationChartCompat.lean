import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt

namespace GlobalTheory.Mean4O.CoverInt

set_option autoImplicit false

theorem chernDens_eq_potDens : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)) (L : HermLB V.p) (P : M.Pot), HessRel ε π L P → ∀ σ, Continuous (π σ) → ∀ (c : AlgChart Y.str (I.ε (ε σ)) e) (c' : AlgChart V.p σ e), (∀ w ∈ c'.e.source, I.pt _ (π σ w) ∈ c.e.source → c'.e w = c.e (I.pt _ (π σ w))) → ∀ w ∈ c'.e.source, I.pt _ (π σ w) ∈ c.e.source → c'.chernDens (L.φ σ) w = potDens I (P (ε σ)) c (π σ w) := by
  intro F _ _ Y V e M I ε π L P hR σ hπ c c' hcc w hw hwc
  rw [AlgChart.chernDens, hR σ c' w hw _ (mem_pick _ w), potDens, ← hcc w hw hwc]
  congr 3
  apply ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr
  have ho : IsOpen (c'.e.target ∩ c'.e.symm ⁻¹' ((π σ) ⁻¹' ((I.pt (ε σ)) ⁻¹' c.e.source))) :=
    c'.e.continuousOn_symm.isOpen_inter_preimage c'.e.open_target
      (c.e.open_source.preimage (I.pt (ε σ)).continuous |>.preimage hπ)
  have hm : c'.e w ∈ c'.e.target ∩ c'.e.symm ⁻¹' ((π σ) ⁻¹' ((I.pt (ε σ)) ⁻¹' c.e.source)) := by
    refine ⟨c'.e.map_source hw, ?_⟩
    simp only [Set.mem_preimage, c'.e.left_inv hw]
    exact hwc
  filter_upwards [ho.mem_nhds hm] with v hv
  have hs : c'.e.symm v ∈ c'.e.source := c'.e.map_target hv.1
  have hv' : v = c.e (I.pt _ (π σ (c'.e.symm v))) := by
    rw [← hcc _ hs hv.2, c'.e.right_inv hv.1]
  have key : c.e.symm v = I.pt _ (π σ (c'.e.symm v)) := by
    conv_lhs => rw [hv']
    exact c.e.left_inv hv.2
  rw [key, Homeomorph.symm_apply_apply]

end GlobalTheory.Mean4O.CoverInt
