import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspSectionValuationBoundPrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_section_valuation_bound_prime : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ (la : AllWt.Weight S.Dw) (g : Rul s.Xo κ.c), g ∈ secZ s.Xo κ.c (exOf S.Dw la 0) → g ∈ suppOn Z → (Φ.C k).val g ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (pl : HeightOneSpectrum (𝓞 κ.c.F)) (p : ℕ), p.Prime → (p : 𝓞 κ.c.F) ∈ pl.asIdeal → ∀ a : ℝ, (∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), (p : 𝓞 D.what₂.LL) ∈ v.asIdeal → ∀ e y, finN Φ k la v e y ((Φ.C k).val g) ≤ NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL) ^ a) → ∀ w ∈ (recVals s.Xo κ.c).1 pl, (((vLa pl (p : κ.c.F) : ℝ) * a : ℝ) : EReal) ≤ w g := by
  first | exact @GlobalTheory.CovHt.Link.le_recVals_of_finN_le | exact GlobalTheory.CovHt.Link.le_recVals_of_finN_le | (intros; apply GlobalTheory.CovHt.Link.le_recVals_of_finN_le <;> assumption)
