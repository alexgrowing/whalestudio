import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoDivisorClassIsoInvariantStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.Vert.Model.FlagPair.GrAgree

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : GlobalTheory.Vert.Model O}

theorem grIso_comm {E E' G G' : Z.X.Modules} {φ : Z.GenIso E E'} {χ : Z.GenIso G G'} {N M : ℕ}
    (P : GlobalTheory.Vert.Model.FlagPair φ N) (Q : GlobalTheory.Vert.Model.FlagPair χ M)
    (k : Fin N) (i : Fin M) (m : P.fl.F k.succ ⟶ Q.fl.F i.succ)
    (m' : P.fl'.F k.succ ⟶ Q.fl'.F i.succ) (u : P.fl.gr k ≅ Q.fl.gr i)
    (u' : P.fl'.gr k ≅ Q.fl'.gr i)
    (hg : Z.genRes.map m ≫ (Q.gen i.succ).hom = (P.gen k.succ).hom ≫ Z.genRes.map m')
    (hu : P.fl.π k ≫ u.hom = m ≫ Q.fl.π i) (hu' : P.fl'.π k ≫ u'.hom = m' ≫ Q.fl'.π i) :
    (P.grIso k).hom ≫ Z.genRes.map u'.hom = Z.genRes.map u.hom ≫ (Q.grIso i).hom := by
  rw [← cancel_epi (Z.genRes.map (P.fl.π k))]
  rw [← Category.assoc, P.π_grIso_hom, Category.assoc, ← Functor.map_comp, hu',
    ← Functor.map_comp_assoc, hu, Functor.map_comp, Functor.map_comp_assoc, Q.π_grIso_hom,
    reassoc_of% hg]

end GlobalTheory.Vert.Model.FlagPair.GrAgree

open GlobalTheory.Vert.Model in

theorem GlobalTheory.Vert.Model.FlagPair.GrAgree.toFPair_agree : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
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
  intro O _ _ _ p _ _ _ Z E E' G G' φ χ N M P Q k i m m' u u' hg hu hu'
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.Vert.smallCls_eq_iff _ _).2 ((P.fl.isVB_gr k).lbIso_det_of_iso u)
  · exact (GlobalTheory.Vert.smallCls_eq_iff _ _).2 ((P.fl'.isVB_gr k).lbIso_det_of_iso u')
  · exact congrArg GlobalTheory.Vert.Model.toQ (GlobalTheory.T.generic_iso_divisor_class_iso_invariant O Z _ _ _ _ 1 _ _ _ _ _ _ u u'
      (GlobalTheory.Vert.Model.FlagPair.GrAgree.grIso_comm P Q k i m m' u u' hg hu hu'))
