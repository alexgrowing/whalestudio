import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteNormSqExponentialBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_norm_sq_exponential_bound : Hypotheses2 → HypothesesH → RegSt → ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (P : Mean4O.PolOf x O.Φ), O.CoreWith x P → 2 < D.R.f * (O.N - 1) → ∀ u : AllWt.Weight O.S.Dw, (∀ τ, StrictAnti (u τ)) → ∀ B : ℝ, 2 ≤ B → ∀ k : O.s.Comp, ∃ C : ℝ, ∀ᶠ r : ℚ in 𝓝[>] 0, ∀ τ : ℕ, 1 ≤ τ → ∀ f ∈ (mbarOf P B (wtR O.L u) r k).secs τ, ∀ (σ : D.what₂.LL →+* ℂ), ∀ y ∈ offBd O.Φ k σ, infSq O.Φ k x (τ • u) σ f y ≤ (Real.exp (C * r * τ) * (mbarOf P B (wtR O.L u) r k).nrmInf σ τ f y) ^ 2 := by
  first | exact @GlobalTheory.CovHt.Link.hodge_le_exp_nrmInf | exact GlobalTheory.CovHt.Link.hodge_le_exp_nrmInf | (intros; apply GlobalTheory.CovHt.Link.hodge_le_exp_nrmInf <;> assumption)
