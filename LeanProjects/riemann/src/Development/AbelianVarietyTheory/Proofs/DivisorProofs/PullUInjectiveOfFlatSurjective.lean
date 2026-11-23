import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.EigenDescent
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDescent

theorem app_injective_of_flat_surjective {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    (V : Y.Opens) : Function.Injective (π.app V) := by
  intro s t h
  apply TopCat.Presheaf.section_ext Y.sheaf V s t
  intro y hy
  obtain ⟨x, rfl⟩ := π.surjective y
  have hinj : Function.Injective (π.stalkMap x) := by
    have hf := Flat.stalkMap π x
    algebraize [(π.stalkMap x).hom]
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (π x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (π x))
      (B := X.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (π x)) (X.presheaf.stalk x)
  apply hinj
  change π.stalkMap x (Y.presheaf.germ V (π x) hy s) = π.stalkMap x (Y.presheaf.germ V (π x) hy t)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, h]

theorem pullU_injective_of_flat_surjective : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y), Flat π → Surjective π →
    ∀ V : Y.Opens, Function.Injective (pullU π V) := by
  intro X Y π _ _ V u v h
  exact Units.ext (app_injective_of_flat_surjective π V (congrArg Units.val h))

end GlobalTheory.EigenDescent
