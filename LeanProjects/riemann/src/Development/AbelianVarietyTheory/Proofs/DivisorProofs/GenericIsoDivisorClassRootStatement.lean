import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoDivisorClassRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_iso_divisor_class_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (Z : GlobalTheory.Vert.Model O) (L L' : Z.X.Modules) (r : ℕ) (hL : GlobalTheory.VB.IsVB L r) (hL' : GlobalTheory.VB.IsVB L' r) (φ : Z.GenIso L L') (e : L' ≅ L) (g : Γ(Z.X, ⊤)) (a : ℕ), 0 < a → IsRootOfP p g a → φ.inv = Z.genRes.map (e.hom ≫ smulHom L g) → a • (GlobalTheory.Vert.Model.GenIso.div φ hL hL').cls = r • Z.divP p := by
  first | exact @GlobalTheory.Vert.Model.GenIso.nsmul_cls_div_of_root | exact GlobalTheory.Vert.Model.GenIso.nsmul_cls_div_of_root | (intros; apply GlobalTheory.Vert.Model.GenIso.nsmul_cls_div_of_root <;> assumption)
