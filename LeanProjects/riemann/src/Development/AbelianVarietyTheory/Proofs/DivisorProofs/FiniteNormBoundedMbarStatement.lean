import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormBoundedMbar
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_norm_bounded_mbar : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (k : s.Comp), ∃ cX : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ, (Function.support cX).Finite ∧ ∀ r : ℚ, 0 < r → ∀ τ : ℕ, 1 ≤ τ → ∀ f ∈ (mbarOf P B (wtR L u) r k).secs τ, ∀ v e y, finN Φ k (τ • u) v e y f ≤ (mbarOf P B (wtR L u) r k).nrmFin v τ f e y * Real.exp (τ * (r * cX v + htLog κ B v * l1 u)) := by
  first | exact @GlobalTheory.CovHt.Link.finN_le_nrmFin_mbarOf | exact GlobalTheory.CovHt.Link.finN_le_nrmFin_mbarOf | (intros; apply GlobalTheory.CovHt.Link.finN_le_nrmFin_mbarOf <;> assumption)
