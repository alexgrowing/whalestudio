import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeFinitePullback
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cap_degree_finite_pullback : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), f.relDim = 0 → 0 < f.fibreDeg 1 ∧ ∀ (d : B.VDivQ) (Q : PicSym B.X), B'.capDeg_vp p (GlobalTheory.Vert.Model.vPullQ f.comp_str d) (picSymPull f.f Q) = f.fibreDeg 1 * B.capDeg_vp p d Q := by
  first | exact @GlobalTheory.VertDegProj.capDeg_vp_vPullQ | exact GlobalTheory.VertDegProj.capDeg_vp_vPullQ | (intros; apply GlobalTheory.VertDegProj.capDeg_vp_vPullQ <;> assumption)
