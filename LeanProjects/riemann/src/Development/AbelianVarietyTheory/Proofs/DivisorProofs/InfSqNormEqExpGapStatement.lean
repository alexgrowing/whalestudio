import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfSqNormEqExpGap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApxGap
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_sq_norm_eq_exp_gap : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (r : ℚ), 0 < r → ∀ (k : s.Comp) (τ : ℕ), 1 ≤ τ → ∀ f ∈ (mbarOf P B (wtR L u) r k).secs τ, ∀ (σ : D.what₂.LL →+* ℂ), ∀ y ∈ offBd Φ k σ, infSq Φ k x (τ • u) σ f y = (mbarOf P B (wtR L u) r k).nrmInf σ τ f y ^ 2 * Real.exp (2 * τ * apxGap Φ L x P B u r k σ y) := by
  first | exact @GlobalTheory.CovHt.Link.infSq_eq_nrmInf_mul_exp | exact GlobalTheory.CovHt.Link.infSq_eq_nrmInf_mul_exp | (intros; apply GlobalTheory.CovHt.Link.infSq_eq_nrmInf_mul_exp <;> assumption)
