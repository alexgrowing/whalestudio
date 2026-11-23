import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralNormLtTop
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Imports

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UpTie

theorem jetInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (Xa : ArchInM X) (Fl : FlatM X Xa), JetInj X Xa Fl := by
  intro E _ _ _ r X Xa Fl f hf hV
  have hb : X.IsBddSec (Xa.Fp + Xa.T • Xa.L) f := hf.1
  exact GlobalTheory.HighOrderVanishing.eq_zero E r X Xa Fl f hb
    (GlobalTheory.isBigO_of_vanS E r X Xa Fl _ f hb.1.1 hV)

end GlobalTheory.UpTie
