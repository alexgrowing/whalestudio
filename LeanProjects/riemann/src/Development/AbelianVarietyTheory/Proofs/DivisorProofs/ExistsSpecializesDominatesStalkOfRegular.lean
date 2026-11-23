import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory

theorem exists_specializes_dominatesStalk_of_regAt (X : Scheme.{0}) [IsIntegral X]
    (V : ValuationSubring X.functionField) (y : X) (hV : ∀ g, RegAt y g → g ∈ V) :
    ∃ z, z ⤳ y ∧ DominatesStalk V z := by
  let ψ : X.presheaf.stalk y →+* V :=
    (algebraMap (X.presheaf.stalk y) X.functionField).codRestrict V.toSubring
      fun a ↦ hV _ ⟨a, rfl⟩
  let l : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk y
  have hl : specAlgebraMap V X.functionField ≫ l = genericFieldPoint X := by
    rw [← specAlgebraMap_fromSpecStalk y, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨l (IsLocalRing.closedPoint V), ?_, dominatesStalk_iff_exists_hom.mpr ⟨l, hl, rfl⟩⟩
  have h := ((IsLocalRing.specializes_closedPoint
    ((Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint V))).map
      (X.fromSpecStalk y).continuous)
  rw [Scheme.fromSpecStalk_closedPoint] at h
  exact h

end GlobalTheory
