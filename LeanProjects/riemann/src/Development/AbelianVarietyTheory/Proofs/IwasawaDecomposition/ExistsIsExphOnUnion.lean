import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenClosureSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothBumpInChartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialControlUniformDeltaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialControlGlueLeftStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialControlGlueRightStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAtLine
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

namespace GlobalTheory.ChernReg.ExphOn

open Set in

theorem exists_isExphOn_union : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [T2Space (CxPts p σ)] [CompactSpace (CxPts p σ)] (R : AnRead p σ d) (a : ChartForm p σ d), IsKaehlerForm R a → ∀ (c : AlgChart p σ d) (E E' : ChartMap p σ d) (W W' K K' : Set (CxPts p σ)) (ε ε' : ℝ), IsOpen W → IsOpen W' → W' ⊆ c.e.source → IsCompact K → IsCompact K' → K ⊆ W → K' ⊆ W' → 0 < ε → 0 < ε' → ExphOn.IsExphOn a E W ε → ExphOn.IsExphOn a E' W' ε' → ∃ (E'' : ChartMap p σ d) (W'' : Set (CxPts p σ)) (ε'' : ℝ), IsOpen W'' ∧ K ∪ K' ⊆ W'' ∧ 0 < ε'' ∧ ExphOn.IsExphOn a E'' W'' ε'' := by
  intro k _ Y p σ d _ _ _ R a ha c E E' W W' K K' ε ε' hW hW' hW'c hK hK' hKW hK'W' hε hε' hE hE'
  obtain ⟨W₀, hW₀o, hKW₀, hW₀W⟩ := exists_open_closure_subset hK hW hKW
  obtain ⟨O₁, hO₁o, hK'O₁, hO₁W'⟩ := exists_open_closure_subset hK' hW' hK'W'
  obtain ⟨ρ, hρc, hρs, hρ01, hρ1, hρsupp⟩ :=
    GlobalTheory.T.exists_smooth_bump_in_chart k Y p σ d c (closure O₁) W' isClosed_closure.isCompact hW' hO₁W' hW'c
  have hW₀W' : W₀ ⊆ W := subset_closure.trans hW₀W
  have hL : IsCompact (closure W₀ ∩ tsupport ρ) := (isClosed_closure.inter (isClosed_tsupport ρ)).isCompact
  have hLW : closure W₀ ∩ tsupport ρ ⊆ W := inter_subset_left.trans hW₀W
  have hLs : closure W₀ ∩ tsupport ρ ⊆ c.e.source := inter_subset_right.trans (hρsupp.trans hW'c)
  obtain ⟨r, hr, hball⟩ := exists_ball_subset c hL hLs
  obtain ⟨δ₁, hδ₁, h₁⟩ := GlobalTheory.T.exponential_control_uniform_delta k Y p σ d R a ha E W ε hε hE c _ r hL hLW hLs hr
  obtain ⟨δ₂, hδ₂, h₂⟩ := GlobalTheory.T.exponential_control_uniform_delta k Y p σ d R a ha E' W' ε' hε' hE' c (tsupport ρ) r
    (isClosed_tsupport ρ).isCompact hρsupp (hρsupp.trans hW'c) hr
  have hε₁ : min (min ε ε') (min δ₁ δ₂) ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hε₂ : min (min ε ε') (min δ₁ δ₂) ≤ ε' := (min_le_left _ _).trans (min_le_right _ _)
  have hε₃ : min (min ε ε') (min δ₁ δ₂) ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₄ : min (min ε ε') (min δ₁ δ₂) ≤ δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hO1 : ∀ y ∈ O₁, ρ y = 1 := fun y hy => hρ1 y (subset_closure hy)
  have hb : ∀ y ∈ W₀ ∩ tsupport ρ, Metric.ball (c.e y) r ⊆ c.e.target :=
    fun y hy => hball y ⟨subset_closure hy.1, hy.2⟩
  have hE1 : ∀ c₀ : AlgChart p σ d, ∀ y ∈ W₀ ∩ tsupport ρ, y ∈ c₀.e.source → ∀ ξ,
      a c₀ y ξ < min (min ε ε') (min δ₁ δ₂) → E c₀ y ξ ∈ c.e.source ∧ c.e (E c₀ y ξ) ∈ Metric.ball (c.e y) r :=
    fun c₀ y hy h0 ξ hξ => h₁ c₀ y ⟨subset_closure hy.1, hy.2⟩ h0 ξ (hξ.trans_le hε₃)
  have hE2 : ∀ c₀ : AlgChart p σ d, ∀ y ∈ tsupport ρ, y ∈ c₀.e.source → ∀ ξ,
      a c₀ y ξ < min (min ε ε') (min δ₁ δ₂) → E' c₀ y ξ ∈ c.e.source ∧ c.e (E' c₀ y ξ) ∈ Metric.ball (c.e y) r :=
    fun c₀ y hy h0 ξ hξ => h₂ c₀ y hy h0 ξ (hξ.trans_le hε₄)
  have hρW : ∀ y, ρ y ≠ 0 → y ∈ W' := fun y h => hρsupp (subset_tsupport _ h)
  refine ⟨glue c ρ E E', W₀ ∪ O₁, min (min ε ε') (min δ₁ δ₂), hW₀o.union hO₁o,
    union_subset_union hKW₀ hK'O₁, lt_min (lt_min hε hε') (lt_min hδ₁ hδ₂), ?_⟩
  exact ⟨glue_trans c ρ hE.trans hE'.trans,
    GlobalTheory.T.exponential_control_glue_left k Y p σ d a c E E' ρ W W' W₀ O₁ ε ε' _ r hE hE' hW₀o hO₁o hW₀W' (subset_closure.trans hO₁W') hρc hρ01 hO1
      hρsupp hW'c hε₁ hε₂ hb hE1 hE2,
    GlobalTheory.T.exponential_control_glue_right k Y p σ d a c E E' ρ W W' W₀ O₁ ε ε' _ r hE hE' hW₀o hO₁o hW₀W' (subset_closure.trans hO₁W') hρc hρ01 hO1
      hρsupp hW'c hε₁ hε₂ hb hE1 hE2 hρs,
    glue_zero c hE.zero hE'.zero hW₀W' hO1 hρW hW'c,
    GlobalTheory.ChernReg.ExphOn.glue_jets k Y p σ d R a ha c E E' ρ W W' W₀ O₁ ε ε' hε hε' hE hE' hW₀W' (subset_closure.trans hO₁W') hO1 hρW hW'c⟩

end GlobalTheory.ChernReg.ExphOn
