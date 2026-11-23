import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem hom_ext_of_localization_atPrime : ∀ (S : Type) [CommRing S] (W : Scheme.{0}) (z z' : Sp S ⟶ W),
    (∀ q : PrimeSpectrum S, spMap (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ z =
      spMap (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ z') → z = z' := by
  intro S _ W z z' h
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun x => ?_
  let q : PrimeSpectrum S := x
  have e : (Sp S).fromSpecStalk q =
      Spec.map (Spec.stalkIso (CommRingCat.of S) q).inv ≫
        spMap (algebraMap S (Localization.AtPrime q.asIdeal)) := by
    rw [Spec.fromSpecStalk_eq, spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of S) (x := q)).symm
  change (Sp S).fromSpecStalk q ≫ z = (Sp S).fromSpecStalk q ≫ z'
  rw [e, Category.assoc, Category.assoc, h q]

end GlobalTheory.FlagMod.FieldFlag
