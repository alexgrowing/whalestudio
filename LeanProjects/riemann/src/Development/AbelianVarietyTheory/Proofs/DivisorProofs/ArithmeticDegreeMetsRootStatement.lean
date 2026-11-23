import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMetsRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_degree_mets_root : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ τ τ' : D.what₂.Tau, ∃ σ : Equiv.Perm D.what₂.Tau, σ τ = τ' ∧ ∀ x : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∃ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ (B R : ℝ) (u : D.what₂.Tau → Fin O.N → ℝ), (GlobalTheory.ShFam.Pad.arIn O.s O.Φ (GlobalTheory.ShFam.metsOf x O.Φ)).arDeg (GlobalTheory.FlagAr.setB O.Y B) R (linRoot (fun ρ i => u (σ ρ) i) ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N + 1)) = (GlobalTheory.ShFam.Pad.arIn O.s O.Φ (GlobalTheory.ShFam.metsOf x' O.Φ)).arDeg (GlobalTheory.FlagAr.setB O.Y B) R (linRoot u ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N + 1)) := by
  first | exact @GlobalTheory.ShFam.GalRelab.arDeg_relabel | exact GlobalTheory.ShFam.GalRelab.arDeg_relabel | (intros; apply GlobalTheory.ShFam.GalRelab.arDeg_relabel <;> assumption)
