import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IteratedDerivCompEqJet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMatrixSmoothInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMatrixChangeOfCoordinatesStatement
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

namespace GlobalTheory.ChernReg.ExphOn

theorem iteratedDeriv_chart_trans : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) (a : ChartForm p σ d), IsKaehlerForm R a → ∀ (c c' : AlgChart p σ d) (u : ℝ → CxPts p σ) (ξ : ReciprocityTheory.L2DbarEstimates.V d), u 0 ∈ c.e.source → u 0 ∈ c'.e.source → ContinuousAt u 0 → ContDiffAt ℝ ∞ (fun t => c.e (u t)) 0 → (∀ n, iteratedDeriv n (fun t => c.e (u t)) 0 = jet (matIn a c) n (c.e (u 0), ξ)) → ∀ n, iteratedDeriv n (fun t => c'.e (u t)) 0 = jet (matIn a c') n (c'.e (u 0), WithLp.toLp 2 (c.dtrans c' (u 0) ξ.ofLp)) := by
  intro k _ Y p σ d R a ha c c' u ξ h0 h0' hu hs hj
  have hU : IsOpen (c.e.target ∩ c.e.symm ⁻¹' c'.e.source) := GlobalTheory.ChartGlue.isOpen_over c.e c'.e.open_source
  have hz : c.e (u 0) ∈ c.e.target ∩ c.e.symm ⁻¹' c'.e.source := GlobalTheory.ChartGlue.mem_over c.e h0 h0'
  have hm := GlobalTheory.T.chart_matrix_smooth_invertible k Y p σ d R a ha c
  have hm' := GlobalTheory.T.chart_matrix_smooth_invertible k Y p σ d R a ha c'
  have key := GlobalTheory.ChernReg.iteratedDeriv_comp_eq_jet d (c.e.target ∩ c.e.symm ⁻¹' c'.e.source) c'.e.target (c'.e ∘ c.e.symm)
    (matIn a c) (matIn a c') hU c'.e.open_target (c.holo_trans c') (fun v hv => c'.e.map_source hv.2) hm'.1
    (fun v hv => hm.2.1 v hv.1) hm'.2.1 (fun v hv => GlobalTheory.T.chart_matrix_change_of_coordinates k Y p σ d R a ha c c' v hv.1 hv.2)
    (c.e (u 0)) hz ξ (fun t => c.e (u t)) hs hj
  have hev : (fun t => c'.e (u t)) =ᶠ[𝓝 0] (c'.e ∘ c.e.symm) ∘ (fun t => c.e (u t)) := by
    have hmem : ∀ᶠ t in 𝓝 (0:ℝ), u t ∈ c.e.source :=
      hu.preimage_mem_nhds (c.e.open_source.mem_nhds h0)
    filter_upwards [hmem] with t ht
    simp only [Function.comp_apply, c.e.left_inv ht]
  intro n
  rw [hev.iteratedDeriv_eq n, key n]
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [Function.comp_apply, c.e.left_inv h0]
  · rfl

end GlobalTheory.ChernReg.ExphOn
