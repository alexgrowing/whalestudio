import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O.Cover

theorem φ_eq_fnMap {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) :
    ∃ hη : V.π (genericPoint V.G) ⤳ genericPoint Y.X, V.φ = GlobalTheory.TrueGeo.SmallSec.fnMap V.π hη := by
  have e : V.π (genericPoint V.G) = genericPoint Y.X := by
    have hc : (spMap V.φ) (IsLocalRing.closedPoint (V.G.presheaf.stalk (genericPoint V.G))) =
        IsLocalRing.closedPoint (Y.X.presheaf.stalk (genericPoint Y.X)) :=
      Subsingleton.elim (α := PrimeSpectrum (Y.X.presheaf.stalk (genericPoint Y.X))) _ _
    refine (congrArg V.π Scheme.fromSpecStalk_closedPoint.symm).trans ?_
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    refine (congrArg (fun f => f (IsLocalRing.closedPoint (V.G.presheaf.stalk (genericPoint V.G)))) V.φ_spec).trans ?_
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    rw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  refine ⟨specializes_of_eq e, ?_⟩
  have key : Spec.map (CommRingCat.ofHom V.φ) =
      Spec.map (Y.X.presheaf.stalkSpecializes (specializes_of_eq e) ≫ V.π.stalkMap (genericPoint V.G)) := by
    rw [← cancel_mono (Y.X.fromSpecStalk (genericPoint Y.X)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact V.φ_spec.symm
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

end GlobalTheory.Mean4O.Cover
