import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenClosureSubset
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.ExphOn

open Set

theorem glue_smooth : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (a : ChartForm p σ d) (c : AlgChart p σ d) (E E' : ChartMap p σ d) (ρ : CxPts p σ → ℝ) (W W' W₀ O₁ : Set (CxPts p σ)) (ε ε' ε'' r : ℝ), ExphOn.IsExphOn a E W ε → ExphOn.IsExphOn a E' W' ε' → IsOpen W₀ → IsOpen O₁ → W₀ ⊆ W → O₁ ⊆ W' → Continuous ρ → (∀ y, 0 ≤ ρ y ∧ ρ y ≤ 1) → (∀ y ∈ O₁, ρ y = 1) → tsupport ρ ⊆ W' → W' ⊆ c.e.source → ε'' ≤ ε → ε'' ≤ ε' → (∀ y ∈ W₀ ∩ tsupport ρ, Metric.ball (c.e y) r ⊆ c.e.target) → (∀ c₀ : AlgChart p σ d, ∀ y ∈ W₀ ∩ tsupport ρ, y ∈ c₀.e.source → ∀ ξ, a c₀ y ξ < ε'' → E c₀ y ξ ∈ c.e.source ∧ c.e (E c₀ y ξ) ∈ Metric.ball (c.e y) r) → (∀ c₀ : AlgChart p σ d, ∀ y ∈ tsupport ρ, y ∈ c₀.e.source → ∀ ξ, a c₀ y ξ < ε'' → E' c₀ y ξ ∈ c.e.source ∧ c.e (E' c₀ y ξ) ∈ Metric.ball (c.e y) r) → ContDiffOn ℝ ∞ (ρ ∘ c.e.symm) c.e.target → ∀ c₀ c' : AlgChart p σ d, ∀ v ∈ c₀.e.target, c₀.e.symm v ∈ W₀ ∪ O₁ → ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, a c₀ (c₀.e.symm v) ξ.ofLp < ε'' → ExphOn.glue c ρ E E' c₀ (c₀.e.symm v) ξ.ofLp ∈ c'.e.source → ContDiffAt ℝ ∞ (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => c'.e (ExphOn.glue c ρ E E' c₀ (c₀.e.symm q.1) q.2.ofLp)) (v, ξ) := by
  intro k _ Y p σ d a c E E' ρ W W' W₀ O₁ ε ε' ε'' r hE hE' hW₀o hO₁o hW₀ hO₁ hρc hρ01 hρ1 hts hW' hε hε' hball hEc
    hE'c hρs c₀ c' v hv hy ξ hξ hg
  have hsymm : ContinuousAt c₀.e.symm v := c₀.e.continuousAt_symm hv
  have hfst : ContinuousAt (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => c₀.e.symm q.1) (v, ξ) :=
    ContinuousAt.comp (g := c₀.e.symm) hsymm continuousAt_fst
  have hy0 : c₀.e.symm v ∈ c₀.e.source := c₀.e.map_target hv
  by_cases h1 : c₀.e.symm v ∈ tsupport ρ
  · by_cases h2 : c₀.e.symm v ∈ O₁
    ·
      have hyW' : c₀.e.symm v ∈ W' := hO₁ h2
      have hξ' : a c₀ (c₀.e.symm v) ξ.ofLp < ε' := hξ.trans_le hε'
      have hE'y := (hE'c c₀ _ h1 hy0 ξ.ofLp hξ).1
      have key : ∀ y' ξ', y' ∈ O₁ → E' c₀ y' ξ' ∈ c.e.source → glue c ρ E E' c₀ y' ξ' = E' c₀ y' ξ' := by
        intro y' ξ' hy' hs
        simp [glue, hρ1 y' hy', c.e.left_inv hs]
      have hg' : E' c₀ (c₀.e.symm v) ξ.ofLp ∈ c'.e.source := by rwa [key _ _ h2 hE'y] at hg
      have hs := hE'.smooth c₀ c' v hv hyW' ξ hξ' hg'
      have ev1 := (hE'.cont c₀ v hv hyW' ξ hξ').preimage_mem_nhds (c.e.open_source.mem_nhds hE'y)
      have ev2 := hfst.preimage_mem_nhds (hO₁o.mem_nhds h2)
      refine hs.congr_of_eventuallyEq ?_
      filter_upwards [ev1, ev2] with q hq1 hq2
      simp only [key _ _ hq2 hq1]
    ·
      have hyW₀ : c₀.e.symm v ∈ W₀ := hy.resolve_right h2
      have hyW : c₀.e.symm v ∈ W := hW₀ hyW₀
      have hyW' : c₀.e.symm v ∈ W' := hts h1
      have hyc : c₀.e.symm v ∈ c.e.source := hW' hyW'
      have hEy := hEc c₀ _ ⟨hyW₀, h1⟩ hy0 ξ.ofLp hξ
      have hE'y := hE'c c₀ _ h1 hy0 ξ.ofLp hξ
      have hf1 := hE.smooth c₀ c v hv hyW ξ (hξ.trans_le hε) hEy.1
      have hf2 := hE'.smooth c₀ c v hv hyW' ξ (hξ.trans_le hε') hE'y.1
      have hgs : ContDiffAt ℝ ∞ (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => ρ (c₀.e.symm q.1)) (v, ξ) := by
        have i1 : ContDiffAt ℝ ∞ (c.e ∘ c₀.e.symm) v := contDiffAt_trans c₀ c hv hyc
        have i2 : ContDiffAt ℝ ∞ (ρ ∘ c.e.symm) ((c.e ∘ c₀.e.symm) v) :=
          hρs.contDiffAt (c.e.open_target.mem_nhds (c.e.map_source hyc))
        have i3 := i2.comp v i1
        have i4 : (ρ ∘ c.e.symm) ∘ (c.e ∘ c₀.e.symm) =ᶠ[𝓝 v] ρ ∘ c₀.e.symm :=
          Filter.eventually_of_mem (hsymm.preimage_mem_nhds (c.e.open_source.mem_nhds hyc)) fun v' hv' => by
            simp only [Function.comp_apply, c.e.left_inv hv']
        exact ContDiffAt.comp (g := ρ ∘ c₀.e.symm) (f := Prod.fst) (v, ξ) (i3.congr_of_eventuallyEq i4.symm) contDiffAt_fst
      set comb : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d := fun q =>
        (1 - ρ (c₀.e.symm q.1)) • c.e (E c₀ (c₀.e.symm q.1) q.2.ofLp) +
          ρ (c₀.e.symm q.1) • c.e (E' c₀ (c₀.e.symm q.1) q.2.ofLp) with hcomb_def
      have hcomb : ContDiffAt ℝ ∞ comb (v, ξ) := ((contDiffAt_const.sub hgs).smul hf1).add (hgs.smul hf2)
      have hcombv : comb (v, ξ) ∈ Metric.ball (c.e (c₀.e.symm v)) r :=
        convex_ball _ _ hEy.2 hE'y.2 (sub_nonneg.2 (hρ01 _).2) (hρ01 _).1 (sub_add_cancel 1 _)
      have hcombt := hball _ ⟨hyW₀, h1⟩ hcombv
      have key : ∀ q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d, E c₀ (c₀.e.symm q.1) q.2.ofLp ∈ c.e.source →
          glue c ρ E E' c₀ (c₀.e.symm q.1) q.2.ofLp = c.e.symm (comb q) := by
        intro q hq
        unfold glue
        split_ifs with h0
        · simp [hcomb_def, h0, c.e.left_inv hq]
        · rfl
      have hg' : c.e.symm (comb (v, ξ)) ∈ c'.e.source := by rwa [key (v, ξ) hEy.1] at hg
      have hmain := (contDiffAt_trans c c' hcombt hg').comp (v, ξ) hcomb
      have ev1 := (hE.cont c₀ v hv hyW ξ (hξ.trans_le hε)).preimage_mem_nhds (c.e.open_source.mem_nhds hEy.1)
      refine hmain.congr_of_eventuallyEq ?_
      filter_upwards [ev1] with q hq
      simp only [Function.comp_apply, key q hq]
  ·
    have hρy : ρ (c₀.e.symm v) = 0 := image_eq_zero_of_notMem_tsupport h1
    have hyW : c₀.e.symm v ∈ W := by
      rcases hy with h | h
      · exact hW₀ h
      · exact absurd (subset_tsupport ρ (by simp [hρ1 _ h])) h1
    have hg' : E c₀ (c₀.e.symm v) ξ.ofLp ∈ c'.e.source := by simpa [glue, hρy] using hg
    have hs := hE.smooth c₀ c' v hv hyW ξ (hξ.trans_le hε) hg'
    have ev := hfst.preimage_mem_nhds ((isClosed_tsupport ρ).isOpen_compl.mem_nhds h1)
    refine hs.congr_of_eventuallyEq ?_
    filter_upwards [ev] with q hq
    simp [glue, image_eq_zero_of_notMem_tsupport hq]

end GlobalTheory.ChernReg.ExphOn
