import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkUniqueCharacterization
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ck_unique_characterization : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r k : ℕ), GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB E' r → IsCk p φ r k (ckP p φ r k) ∧ (∀ f, IsCk p φ r k f → f = ckP p φ r k) ∧ ∀ (P : GlobalTheory.Vert.Model.FlagPair φ r) (Q : PicSym B.X), ckP p φ r k Q = ck (P.toFPair p) k Q := by
  first | exact @GlobalTheory.CkPairWd.ckP_spec | exact GlobalTheory.CkPairWd.ckP_spec | (intros; apply GlobalTheory.CkPairWd.ckP_spec <;> assumption)
