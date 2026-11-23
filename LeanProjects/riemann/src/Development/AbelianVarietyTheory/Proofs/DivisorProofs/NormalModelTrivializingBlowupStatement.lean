import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowup
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_model_trivializing_blowup : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (n : ℕ) (r : Fin n → ℕ) (E E' : Fin n → B.X.Modules) (φ : ∀ i, B.GenIso (E i) (E' i)), (∀ i, GlobalTheory.VB.IsVB (E i) (r i) ∧ GlobalTheory.VB.IsVB (E' i) (r i)) → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ∀ i, Nonempty (GlobalTheory.Vert.Model.FlagPair ((φ i).pull f.comp_str) (r i)) := by
  first | exact @GlobalTheory.FlagPairExists.exists_normal_modification_flagPair | exact GlobalTheory.FlagPairExists.exists_normal_modification_flagPair | (intros; apply GlobalTheory.FlagPairExists.exists_normal_modification_flagPair <;> assumption)
