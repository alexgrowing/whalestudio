import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkAdditiveComposition
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ck_additive_composition : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' E'' : B.X.Modules) (φ : B.GenIso E E') (φ' : B.GenIso E' E'') (r k : ℕ), GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB E' r → GlobalTheory.VB.IsVB E'' r → ckP p (φ ≪≫ φ') r k = ckP p φ r k + ckP p φ' r k ∧ ckP p φ.symm r k = -ckP p φ r k := by
  first | exact @GlobalTheory.CkChain.ckP_trans | exact GlobalTheory.CkChain.ckP_trans | (intros; apply GlobalTheory.CkChain.ckP_trans <;> assumption)
