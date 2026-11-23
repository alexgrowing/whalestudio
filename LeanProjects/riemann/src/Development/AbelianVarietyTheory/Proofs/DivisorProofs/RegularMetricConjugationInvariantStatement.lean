import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularMetricConjugationInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_metric_conjugation_invariant : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (σ σ' : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin O.N → ℝ) (t : ℝ) (y : Pts (O.var c) σ) (y' : Pts (O.var c) σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → O.met.reg c σ' u t y' = O.met.reg c σ u t y := by
  first | exact @GlobalTheory.Mean4O.Setup.reg_conj | exact GlobalTheory.Mean4O.Setup.reg_conj | (intros; apply GlobalTheory.Mean4O.Setup.reg_conj <;> assumption)
