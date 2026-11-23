import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerKilledOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledNear

def FibreKilled (d : ℕ) {S' : Scheme.{0}} (G : Over S') [GrpObj G] (P : LB (G2 G).left) (s : S') : Prop :=
  ∀ (T' : Over S') (x : T' ⟶ G),
    (∃ f : T'.left ⟶ Spec (S'.residueField s), T'.hom = f ≫ S'.fromSpecResidueField s) →
    (∃ c : (P.pull (lift (snd G T' ≫ x) (fst G T')).left).Gen, c.IsGen) → x ^ d = 1

end GlobalTheory.KerKilledNear
