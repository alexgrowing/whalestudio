import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocMapOfMem
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.ExphLoc

open Set GlobalTheory.ChartGlue

theorem locMap_eventuallyEq_symm : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) (a : ChartForm p σ d), IsKaehlerForm R a → ∀ (c c₀ : AlgChart p σ d) (f : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (W : Set (CxPts p σ)) (ε : ℝ), ContDiff ℝ ∞ f → W ⊆ c.e.source → (∀ y ∈ W, ∀ η : ReciprocityTheory.L2DbarEstimates.V d, a c y η.ofLp < ε → f (c.e y, η) ∈ c.e.target) → ∀ v ∈ c₀.e.target, c₀.e.symm v ∈ W → ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, a c₀ (c₀.e.symm v) ξ.ofLp < ε → ∃ Φ : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d, ContDiffAt ℝ ∞ Φ (v, ξ) ∧ Φ (v, ξ) ∈ c.e.target ∧ (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => GlobalTheory.ChernReg.ExphLoc.locMap c f c₀ (c₀.e.symm q.1) q.2.ofLp) =ᶠ[𝓝 (v, ξ)] fun q => c.e.symm (Φ q) := by
  intro k _ Y p σ d R a ha c c₀ f W ε hf hWs hW v hv hvW ξ hξ
  set τ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d := c.e ∘ c₀.e.symm with hτdef
  set O : Set (ReciprocityTheory.L2DbarEstimates.V d) := c₀.e.target ∩ c₀.e.symm ⁻¹' c.e.source with hOdef
  have hO : IsOpen O := isOpen_over c₀.e c.e.open_source
  have hvO : v ∈ O := ⟨hv, hWs hvW⟩
  have hτ : ContDiffAt ℂ ∞ τ v :=
    (((contDiffOn_piLp 2).2 fun i => ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn d _ _ hO
      (differentiableOn_euclidean.1 (c₀.holo_trans c) i)).contDiffAt (hO.mem_nhds hvO)).of_le le_rfl
  have hDτ : ContDiffAt ℂ ∞ (fderiv ℂ τ) v := hτ.fderiv_right (by simp)
  let g : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d :=
    fun q => (τ q.1, fderiv ℂ τ q.1 q.2)
  have hg : ContDiffAt ℂ ∞ g (v, ξ) :=
    (hτ.comp (v, ξ) contDiffAt_fst).prodMk ((hDτ.comp (v, ξ) contDiffAt_fst).clm_apply contDiffAt_snd)
  let Φ : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d := fun q => f (g q)
  have hΦ : ContDiffAt ℝ ∞ Φ (v, ξ) := hf.contDiffAt.comp (v, ξ) (hg.restrict_scalars ℝ)

  have key : ∀ u ∈ c₀.e.target, ∀ w : ReciprocityTheory.L2DbarEstimates.V d,
      WithLp.toLp 2 (c₀.dtrans c (c₀.e.symm u) w.ofLp) = fderiv ℂ τ u w := by
    intro u hu w
    have hr : c₀.e (c₀.e.symm u) = u := c₀.e.right_inv hu
    show WithLp.toLp 2 (fun b => fderiv ℂ (c.e ∘ c₀.e.symm) (c₀.e (c₀.e.symm u)) (WithLp.toLp 2 w.ofLp) b) = _
    rw [hr]
  have keyf : ∀ u ∈ O, ∀ w : ReciprocityTheory.L2DbarEstimates.V d,
      f (c.e (c₀.e.symm u), WithLp.toLp 2 (c₀.dtrans c (c₀.e.symm u) w.ofLp)) = Φ (u, w) := by
    intro u hu w
    rw [key u hu.1 w]
    rfl
  have hmem : Φ (v, ξ) ∈ c.e.target := by
    have hy : c₀.e.symm v ∈ c₀.e.source := c₀.e.map_target hv
    have hlt : a c (c₀.e.symm v) (WithLp.toLp 2 (c₀.dtrans c (c₀.e.symm v) ξ.ofLp)).ofLp < ε := by
      rw [WithLp.ofLp_toLp, ← ha.trans hy (hWs hvW)]
      exact hξ
    have := hW _ hvW _ hlt
    rwa [keyf v hvO ξ] at this
  refine ⟨Φ, hΦ, hmem, ?_⟩
  have h1 : ∀ᶠ q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d in 𝓝 (v, ξ), q.1 ∈ O :=
    continuousAt_fst.preimage_mem_nhds (hO.mem_nhds hvO)
  have h2 : ∀ᶠ q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d in 𝓝 (v, ξ), Φ q ∈ c.e.target :=
    hΦ.continuousAt.preimage_mem_nhds (c.e.open_target.mem_nhds hmem)
  filter_upwards [h1, h2] with q hq1 hq2
  have e := keyf q.1 hq1 q.2
  simp only [Prod.mk.eta] at e
  rw [locMap_of_mem c c₀ f ⟨hq1.2, by rwa [e]⟩, e]

end GlobalTheory.ChernReg.ExphLoc
