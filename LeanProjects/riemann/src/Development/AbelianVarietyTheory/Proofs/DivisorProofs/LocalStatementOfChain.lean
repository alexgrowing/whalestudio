import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodLocalFinImpLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFiniteOfChain
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

theorem GlobalTheory.MixedLocalChains.localSt_of_chainSt : ChainSt → LocalSt := by
  intro h D O hc p _ h2 hu hl W hW jc hpin z
  obtain ⟨o, -, hper, himp⟩ := exists_period_localFin_imp_local D p
  exact himp _ _ _ (GlobalTheory.T.local_finite_of_chain _ _ _ _ _ _ _ _ _ hW z jc o hper (h D O hc p h2 hu hl W hW jc hpin z o))
