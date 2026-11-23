import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem proper_lift_trait : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), IsProper π → ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (f : V →+* V') (fK : FractionRing V →+* FractionRing V'), (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) → ∀ (ξ : Sp V ⟶ X) (y : Sp (FractionRing V') ⟶ Y), y ≫ π = spMap fK ≫ jK V ≫ ξ → ∃ ξ' : Sp V' ⟶ Y, ξ' ≫ π = spMap f ≫ ξ ∧ jK V' ≫ ξ' = y := by
  intro X Y π hπ V V' _ _ _ _ _ f fK hf ξ y hy
  have hsq : jK V' ≫ spMap f = spMap fK ≫ jK V := by
    have e : fK.comp (algebraMap V (FractionRing V)) = (algebraMap V' (FractionRing V')).comp f :=
      RingHom.ext hf
    exact (spMap_comp f (algebraMap V' (FractionRing V'))).symm.trans
      ((congrArg spMap e.symm).trans (spMap_comp (algebraMap V (FractionRing V)) fK))
  have h : y ≫ π = jK V' ≫ (spMap f ≫ ξ) := by
    rw [hy, ← Category.assoc, ← hsq, Category.assoc]
  obtain ⟨x, hx1, hx2⟩ := val_exists (R := V') π y (spMap f ≫ ξ) h
  exact ⟨x, hx2, hx1⟩

end GlobalTheory
