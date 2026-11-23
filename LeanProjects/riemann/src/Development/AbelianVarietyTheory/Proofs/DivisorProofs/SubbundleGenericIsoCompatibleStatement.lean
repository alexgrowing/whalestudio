import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleGenericIsoCompatible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subbundle_generic_iso_compatible : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O) (E E' E'' K K' K'' : Z.X.Modules) (φ : Z.GenIso E E') (φ' : Z.GenIso E' E'') (i : K ⟶ E) (i' : K' ⟶ E') (i'' : K'' ⟶ E'') (ψ : Z.GenIso K K') (ψ' : Z.GenIso K' K'') (r : ℕ), GlobalTheory.VB.IsSubbundle i → GlobalTheory.VB.IsSubbundle i' → GlobalTheory.VB.IsSubbundle i'' → GlobalTheory.VB.IsVB E (r + 1) → GlobalTheory.VB.IsVB E' (r + 1) → GlobalTheory.VB.IsVB E'' (r + 1) → ψ.hom ≫ Z.genRes.map i' = Z.genRes.map i ≫ φ.hom → ψ'.hom ≫ Z.genRes.map i'' = Z.genRes.map i' ≫ φ'.hom → ∀ (P : GlobalTheory.Vert.Model.FlagPair ψ r) (Q : GlobalTheory.Vert.Model.FlagPair ψ' r), Q.fl = P.fl' → ∃ (P₁ : GlobalTheory.Vert.Model.FlagPair φ (r + 1)) (Q₁ : GlobalTheory.Vert.Model.FlagPair φ' (r + 1)), Q₁.fl = P₁.fl' := by
  first | exact @GlobalTheory.Vert.Model.FlagPair.exists_extend_chain | exact GlobalTheory.Vert.Model.FlagPair.exists_extend_chain | (intros; apply GlobalTheory.Vert.Model.FlagPair.exists_extend_chain <;> assumption)
