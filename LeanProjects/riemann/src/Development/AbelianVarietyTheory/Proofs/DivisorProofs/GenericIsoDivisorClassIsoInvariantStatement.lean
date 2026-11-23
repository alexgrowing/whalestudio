import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoDivisorClassIsoInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_iso_divisor_class_iso_invariant : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Z : GlobalTheory.Vert.Model O) (L L' M M' : Z.X.Modules) (r : ℕ) (hL : GlobalTheory.VB.IsVB L r)
    (hL' : GlobalTheory.VB.IsVB L' r) (hM : GlobalTheory.VB.IsVB M r) (hM' : GlobalTheory.VB.IsVB M' r)
    (φ : Z.GenIso L L') (χ : Z.GenIso M M') (e : L ≅ M) (e' : L' ≅ M'),
    φ.hom ≫ Z.genRes.map e'.hom = Z.genRes.map e.hom ≫ χ.hom →
    (GlobalTheory.Vert.Model.GenIso.div φ hL hL').cls = (GlobalTheory.Vert.Model.GenIso.div χ hM hM').cls := by
  first | exact @GlobalTheory.Vert.Model.GenIso.cls_div_eq_of_iso | exact GlobalTheory.Vert.Model.GenIso.cls_div_eq_of_iso | (intros; apply GlobalTheory.Vert.Model.GenIso.cls_div_eq_of_iso <;> assumption)
