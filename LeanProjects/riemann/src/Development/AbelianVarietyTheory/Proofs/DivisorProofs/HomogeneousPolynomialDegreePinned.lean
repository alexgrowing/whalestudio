import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.LocalEmbeddings.GeoAll
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
theorem _root_.GlobalTheory.T.homogeneous_polynomial_degree_pinned : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → UnramE D p → p ∉ O.Y.lev → ∀ (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (jc : KW p →+* ℂ), Pin W jc → ∀ (z : AdmAt O.S O.κ (Fact.out : p.Prime) hW) (P : MvPolynomial (Rt D.what₂.Tau O.N) ℚ), P.IsHomogeneous (dimFl D.what₂.Tau O.N) → haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW; ((∑ C ∈ Finset.univ.filter (fun C : (nmodel z.Z).Comp => ((nmodel z.Z).comp C).relDim = dimFl D.what₂.Tau O.N), ((nmodel z.Z).comp C).toBase.fibreDeg (picSymPull ((nmodel z.Z).compι C) (aeval (fun x => (mdlOf z jc).Z.c1 (rootOf z jc (false, x))) P)) : ℚ) : ℝ) = ((mdlOf z jc).cov : ℝ) * O.Y.chern (toR P) :=
  fun hP _ D O _ p _ _ _ _ W hW jc _ z P h => GlobalTheory.ConsGeo.GenDeg.geoAll hP D O p W hW jc z P h
