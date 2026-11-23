import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbarSemipositiveNefSmallR
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mbar_semipositive_nef_small_r : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegSt → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) → ∀ (u : D.what₂.Tau → Fin O.N → ℝ) (g : ℝ), IsRat O.Y u → WeightThresholdDefs.WeightHyp O.Y u g → ∀ᶠ r : ℚ in 𝓝[>] 0, ∀ k : O.s.Comp, (O.Mb (WeightThresholdDefs.bigB0 O.Y u g) u r k).SemiPos ∧ (O.Mb (WeightThresholdDefs.bigB0 O.Y u g) u r k).NefFib := by
  first | exact @GlobalTheory.CovHt.Link.approx_semipos_nefFib | exact GlobalTheory.CovHt.Link.approx_semipos_nefFib | (intros; apply GlobalTheory.CovHt.Link.approx_semipos_nefFib <;> assumption)
