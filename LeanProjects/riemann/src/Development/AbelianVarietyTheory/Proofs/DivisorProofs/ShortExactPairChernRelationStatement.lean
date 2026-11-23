import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactPairChernRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_exact_pair_chern_relation : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Z : GlobalTheory.Vert.Model O) (A B C A' B' C' : Z.X.Modules) (f : A ⟶ B) (g : B ⟶ C)
    (hfg : f ≫ g = 0) (f' : A' ⟶ B') (g' : B' ⟶ C') (hfg' : f' ≫ g' = 0),
    (ShortComplex.mk f g hfg).ShortExact → (ShortComplex.mk f' g' hfg').ShortExact →
    ∀ (s s' : ℕ), GlobalTheory.VB.IsVB C s → GlobalTheory.VB.IsVB C' s' →
    ∀ [A.IsQuasicoherent] [B.IsQuasicoherent] [A'.IsQuasicoherent] [B'.IsQuasicoherent]
    (φB : Z.GenIso B B') (φC : Z.GenIso C C'),
    Z.genRes.map g ≫ φC.hom = φB.hom ≫ Z.genRes.map g' →
    ∃ γ : Z.GenIso A A', γ.hom ≫ Z.genRes.map f' = Z.genRes.map f ≫ φB.hom := by
  first | exact @GlobalTheory.Vert.Model.exists_genIso_ker | exact GlobalTheory.Vert.Model.exists_genIso_ker | (intros; apply GlobalTheory.Vert.Model.exists_genIso_ker <;> assumption)
