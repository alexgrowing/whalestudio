import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairMorphismCompatibility
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_pair_morphism_compatibility : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]
    (Z : GlobalTheory.Vert.Model O) (E E' G G' : Z.X.Modules) (φ : Z.GenIso E E') (χ : Z.GenIso G G')
    (N M : ℕ) (P : GlobalTheory.Vert.Model.FlagPair φ N) (Q : GlobalTheory.Vert.Model.FlagPair χ M)
    (k : Fin N) (i : Fin M) (m : P.fl.F k.succ ⟶ Q.fl.F i.succ)
    (m' : P.fl'.F k.succ ⟶ Q.fl'.F i.succ) (u : P.fl.gr k ≅ Q.fl.gr i)
    (u' : P.fl'.gr k ≅ Q.fl'.gr i),
    Z.genRes.map m ≫ (Q.gen i.succ).hom = (P.gen k.succ).hom ≫ Z.genRes.map m' →
    P.fl.π k ≫ u.hom = m ≫ Q.fl.π i → P.fl'.π k ≫ u'.hom = m' ≫ Q.fl'.π i →
    (P.toFPair p).x k = (Q.toFPair p).x i ∧ (P.toFPair p).x' k = (Q.toFPair p).x' i ∧
      (P.toFPair p).Dv k = (Q.toFPair p).Dv i := by
  first | exact @GlobalTheory.Vert.Model.FlagPair.GrAgree.toFPair_agree | exact GlobalTheory.Vert.Model.FlagPair.GrAgree.toFPair_agree | (intros; apply GlobalTheory.Vert.Model.FlagPair.GrAgree.toFPair_agree <;> assumption)
