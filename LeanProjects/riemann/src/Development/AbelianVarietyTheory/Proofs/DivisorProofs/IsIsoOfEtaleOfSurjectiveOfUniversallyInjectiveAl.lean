import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isIso_of_etale_of_surjective_of_universallyInjective :
    ∀ (X Z : Scheme.{0}) (h : X ⟶ Z), Etale h → Surjective h → UniversallyInjective h → IsIso h := by
  intro X Z h het hs hui
  have hd : Surjective (pullback.diagonal h) := (UniversallyInjective.iff_diagonal h).1 hui
  have : IsIso (pullback.diagonal h) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hd⟩
  have : Mono h := (pullback.isIso_diagonal_iff h).1 this
  have : IsOpenImmersion h := IsOpenImmersion.of_flat_of_mono h
  exact (isIso_iff_isOpenImmersion_and_surjective h).2 ⟨this, hs⟩

end GlobalTheory.Mum
