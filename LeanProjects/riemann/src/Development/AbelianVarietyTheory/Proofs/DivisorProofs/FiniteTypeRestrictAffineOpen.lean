import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory.ProjVar.Var

theorem finiteType_restrict_affineOpen : ∀ (F : Type) [Field F] (Y : Var F) (V : Y.X.Opens), IsAffineOpen V →
    ((Y.X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp (algebraMap F Γ(Y.X, ⊤))).FiniteType := by
  intro F _ Y V hV
  have hft := Y.str.finiteType_appLE (isAffineOpen_top (Sp F)) hV le_top
  have key : (Y.X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp (algebraMap F Γ(Y.X, ⊤)) =
      (Y.str.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom := by
    ext a
    simp only [RingHom.comp_apply, Var.algebraMap_Γ, Scheme.Hom.appLE]
    rfl
  rw [key]
  exact hft.comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of F)).inv).2)

end GlobalTheory.ProjVar.Var
