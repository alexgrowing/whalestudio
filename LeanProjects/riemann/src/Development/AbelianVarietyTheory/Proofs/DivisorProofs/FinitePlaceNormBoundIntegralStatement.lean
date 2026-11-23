import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceNormBoundIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_place_norm_bound_integral : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (f : (Φ.C k).Y.Fn), f ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (p : ℕ) [Fact p.Prime] (a : ℝ), (∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), (p : 𝓞 D.what₂.LL) ∈ v.asIdeal → ∀ e y, finN Φ k la v e y f ≤ NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL) ^ a) → ∀ (ι : AlgebraicClosure D.what₂.LL →+* ℂ_[p]) (y : AlgPt (Φ.C k).Y), drAt Φ k la p (spMap ι ≫ y.1) f ≤ (p : ℝ) ^ (-a) := by
  first | exact @GlobalTheory.CovHt.Link.drAt_le_of_finN_le | exact GlobalTheory.CovHt.Link.drAt_le_of_finN_le | (intros; apply GlobalTheory.CovHt.Link.drAt_le_of_finN_le <;> assumption)
