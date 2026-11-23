import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoFlagLiftExists
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_iso_flag_lift_exists : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (Z : GlobalTheory.Vert.Model O) (E E' : Z.X.Modules) (r : ℕ) (φ : Z.GenIso E E') (e : E' ≅ E) (g : Γ(Z.X, ⊤)) (a : ℕ), 0 < a → IsRootOfP p g a → φ.inv = Z.genRes.map (e.hom ≫ smulHom E g) → ∀ fl : GlobalTheory.Vert.Flag E r, ∃ P : GlobalTheory.Vert.Model.FlagPair φ r, P.fl = fl ∧ ∀ i, ∃ ei : P.fl'.gr i ≅ P.fl.gr i, (P.grIso i).inv = Z.genRes.map (ei.hom ≫ smulHom (P.fl.gr i) g) := by
  first | exact @GlobalTheory.MixedLocalChains.exists_flagPair_of_root | exact GlobalTheory.MixedLocalChains.exists_flagPair_of_root | (intros; apply GlobalTheory.MixedLocalChains.exists_flagPair_of_root <;> assumption)
