import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairExtendsByOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_extends_by_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O) (E E' K K' : Z.X.Modules) (φ : Z.GenIso E E') (i : K ⟶ E) (i' : K' ⟶ E') (ψ : Z.GenIso K K') (r : ℕ), GlobalTheory.VB.IsSubbundle i → GlobalTheory.VB.IsSubbundle i' → GlobalTheory.VB.IsVB E (r + 1) → GlobalTheory.VB.IsVB E' (r + 1) → ψ.hom ≫ Z.genRes.map i' = Z.genRes.map i ≫ φ.hom → GlobalTheory.Vert.Model.FlagPair ψ r → Nonempty (GlobalTheory.Vert.Model.FlagPair φ (r + 1)) := by
  first | exact @GlobalTheory.Vert.Model.FlagPair.nonempty_extend | exact GlobalTheory.Vert.Model.FlagPair.nonempty_extend | (intros; apply GlobalTheory.Vert.Model.FlagPair.nonempty_extend <;> assumption)
