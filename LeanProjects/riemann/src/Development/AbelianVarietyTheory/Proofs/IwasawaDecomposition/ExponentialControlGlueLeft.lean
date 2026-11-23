import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenClosureSubset
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

namespace GlobalTheory.ChernReg.ExphOn

theorem glue_cont : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (a : ChartForm p σ d) (c : AlgChart p σ d) (E E' : ChartMap p σ d) (ρ : CxPts p σ → ℝ) (W W' W₀ O₁ : Set (CxPts p σ)) (ε ε' ε'' r : ℝ), ExphOn.IsExphOn a E W ε → ExphOn.IsExphOn a E' W' ε' → IsOpen W₀ → IsOpen O₁ → W₀ ⊆ W → O₁ ⊆ W' → Continuous ρ → (∀ y, 0 ≤ ρ y ∧ ρ y ≤ 1) → (∀ y ∈ O₁, ρ y = 1) → tsupport ρ ⊆ W' → W' ⊆ c.e.source → ε'' ≤ ε → ε'' ≤ ε' → (∀ y ∈ W₀ ∩ tsupport ρ, Metric.ball (c.e y) r ⊆ c.e.target) → (∀ c₀ : AlgChart p σ d, ∀ y ∈ W₀ ∩ tsupport ρ, y ∈ c₀.e.source → ∀ ξ, a c₀ y ξ < ε'' → E c₀ y ξ ∈ c.e.source ∧ c.e (E c₀ y ξ) ∈ Metric.ball (c.e y) r) → (∀ c₀ : AlgChart p σ d, ∀ y ∈ tsupport ρ, y ∈ c₀.e.source → ∀ ξ, a c₀ y ξ < ε'' → E' c₀ y ξ ∈ c.e.source ∧ c.e (E' c₀ y ξ) ∈ Metric.ball (c.e y) r) → ∀ c₀ : AlgChart p σ d, ∀ v ∈ c₀.e.target, c₀.e.symm v ∈ W₀ ∪ O₁ → ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, a c₀ (c₀.e.symm v) ξ.ofLp < ε'' → ContinuousAt (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => ExphOn.glue c ρ E E' c₀ (c₀.e.symm q.1) q.2.ofLp) (v, ξ) := by
  intro k _ Y p σ d a c E E' ρ W W' W₀ O₁ ε ε' ε'' r hE hE' hW₀o hO₁o hW₀ hO₁ hρ hρ01 hρ1 htW' hW' hε hε' hrt hEr hE'r c₀ v hv hy ξ hξ
  have hy₀ : (c₀.e.symm v) ∈ c₀.e.source := c₀.e.map_target hv
  have hs : ContinuousAt (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => c₀.e.symm q.1) (v, ξ) :=
    (c₀.e.continuousAt_symm hv).comp continuousAt_fst
  have hev : ∀ S : Set (CxPts p σ), IsOpen S → (c₀.e.symm v) ∈ S →
      ∀ᶠ q in 𝓝 (v, ξ), c₀.e.symm (q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d).1 ∈ S :=
    fun S hS hyS => hs (hS.mem_nhds hyS)
  have hO₁t : ∀ z ∈ O₁, z ∈ tsupport ρ := fun z hz =>
    subset_tsupport ρ (by rw [Function.mem_support, hρ1 z hz]; exact one_ne_zero)
  by_cases hyO : (c₀.e.symm v) ∈ O₁
  ·
    have hc' := hE'.cont c₀ v hv (hO₁ hyO) ξ (hξ.trans_le hε')
    have hsrc := (hE'r c₀ (c₀.e.symm v) (hO₁t (c₀.e.symm v) hyO) hy₀ ξ.ofLp hξ).1
    refine hc'.congr ?_
    filter_upwards [hev O₁ hO₁o hyO, hc' (c.e.open_source.mem_nhds hsrc)] with q hq hq'
    simp only [glue, hρ1 _ hq, one_ne_zero, if_false, sub_self, zero_smul, zero_add, one_smul]
    exact (c.e.left_inv hq').symm
  have hyW₀ : (c₀.e.symm v) ∈ W₀ := hy.resolve_right hyO
  have hc := hE.cont c₀ v hv (hW₀ hyW₀) ξ (hξ.trans_le hε)
  by_cases hyt : (c₀.e.symm v) ∈ tsupport ρ
  ·
    have hc' := hE'.cont c₀ v hv (htW' hyt) ξ (hξ.trans_le hε')
    have h1 := hEr c₀ (c₀.e.symm v) ⟨hyW₀, hyt⟩ hy₀ ξ.ofLp hξ
    have h2 := hE'r c₀ (c₀.e.symm v) hyt hy₀ ξ.ofLp hξ
    have hρs : ContinuousAt (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => ρ (c₀.e.symm q.1)) (v, ξ) :=
      hρ.continuousAt.comp hs
    have hcF : ContinuousAt (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => c.e (E c₀ (c₀.e.symm q.1) q.2.ofLp)) (v, ξ) :=
      ContinuousAt.comp (x := (v, ξ)) (f := fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => E c₀ (c₀.e.symm q.1) q.2.ofLp) (c.e.continuousAt h1.1) hc
    have hcF' : ContinuousAt (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => c.e (E' c₀ (c₀.e.symm q.1) q.2.ofLp)) (v, ξ) :=
      ContinuousAt.comp (x := (v, ξ)) (f := fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => E' c₀ (c₀.e.symm q.1) q.2.ofLp) (c.e.continuousAt h2.1) hc'
    have hcomb : ContinuousAt (fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d =>
        (1 - ρ (c₀.e.symm q.1)) • c.e (E c₀ (c₀.e.symm q.1) q.2.ofLp) +
          ρ (c₀.e.symm q.1) • c.e (E' c₀ (c₀.e.symm q.1) q.2.ofLp)) (v, ξ) :=
      ((continuousAt_const.sub hρs).smul hcF).add (hρs.smul hcF')
    have hmem : (1 - ρ (c₀.e.symm v)) • c.e (E c₀ (c₀.e.symm v) ξ.ofLp) + ρ (c₀.e.symm v) • c.e (E' c₀ (c₀.e.symm v) ξ.ofLp) ∈ Metric.ball (c.e (c₀.e.symm v)) r :=
      convex_ball (c.e (c₀.e.symm v)) r h1.2 h2.2 (sub_nonneg.2 (hρ01 (c₀.e.symm v)).2) (hρ01 (c₀.e.symm v)).1 (sub_add_cancel 1 _)
    have hsym : ContinuousAt c.e.symm ((1 - ρ (c₀.e.symm v)) • c.e (E c₀ (c₀.e.symm v) ξ.ofLp) + ρ (c₀.e.symm v) • c.e (E' c₀ (c₀.e.symm v) ξ.ofLp)) :=
      c.e.continuousAt_symm (hrt (c₀.e.symm v) ⟨hyW₀, hyt⟩ hmem)
    have hall := ContinuousAt.comp (x := (v, ξ)) (f := fun q : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d =>
        (1 - ρ (c₀.e.symm q.1)) • c.e (E c₀ (c₀.e.symm q.1) q.2.ofLp) +
          ρ (c₀.e.symm q.1) • c.e (E' c₀ (c₀.e.symm q.1) q.2.ofLp)) hsym hcomb
    refine hall.congr ?_
    filter_upwards [hc (c.e.open_source.mem_nhds h1.1)] with q hq
    simp only [Function.comp_apply, glue]
    split_ifs with h0
    · rw [h0, sub_zero, zero_smul, add_zero, one_smul]
      exact c.e.left_inv hq
    · rfl
  ·
    refine hc.congr ?_
    filter_upwards [hev (tsupport ρ)ᶜ (isClosed_tsupport ρ).isOpen_compl hyt] with q hq
    simp only [glue, image_eq_zero_of_notMem_tsupport hq, if_true]

end GlobalTheory.ChernReg.ExphOn
