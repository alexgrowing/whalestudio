import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoNormalModel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_iso_normal_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' E'' : B.X.Modules) (φ : B.GenIso E E') (φ' : B.GenIso E' E'') (r : ℕ), GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB E' r → GlobalTheory.VB.IsVB E'' r → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ∃ (P : GlobalTheory.Vert.Model.FlagPair (GlobalTheory.Vert.Model.GenIso.pull f.comp_str φ) r) (P' : GlobalTheory.Vert.Model.FlagPair (GlobalTheory.Vert.Model.GenIso.pull f.comp_str φ') r), P'.fl = P.fl' := by
  first | exact @GlobalTheory.ThreeFlag.exists_normal_modification_flagPair_chain | exact GlobalTheory.ThreeFlag.exists_normal_modification_flagPair_chain | (intros; apply GlobalTheory.ThreeFlag.exists_normal_modification_flagPair_chain <;> assumption)
